open Syntax
open BatPervasives

include Log.Make(struct let name = "srk.linear" end)

module IntSet = SrkUtil.Int.Set

module ZZVector = struct
  include Ring.MakeVector(ZZ)

  let pp formatter vec =
    let pp_elt formatter (v, k) = Format.fprintf formatter "%d:%a" k ZZ.pp v in
    enum vec
    |> Format.fprintf formatter "[@[%a@]]" (SrkUtil.pp_print_enum pp_elt)

  let pp_term pp_dim formatter vec =
    let pp_elt formatter (v, k) = Format.fprintf formatter "%a * %a" ZZ.pp v pp_dim k in
    if is_zero vec then
      Format.pp_print_string formatter "0"
    else
      enum vec
      |> Format.fprintf formatter "[@[%a@]]" (SrkUtil.pp_print_enum pp_elt)

  let show = SrkUtil.mk_show pp
  let compare = compare ZZ.compare
  let hash = hash (fun (dim, coeff) -> Hashtbl.hash (dim, ZZ.hash coeff))
end

module QQVector = struct
  include Ring.MakeVector(QQ)

  let pp formatter vec =
    let pp_elt formatter (v, k) = Format.fprintf formatter "%d:%a" k QQ.pp v in
    enum vec
    |> Format.fprintf formatter "[@[%a@]]" (SrkUtil.pp_print_enum pp_elt)

  let pp_term pp_dim formatter vec =
    let pp_elt formatter (v, k) = Format.fprintf formatter "%a * %a" QQ.pp v pp_dim k in
    if is_zero vec then
      Format.pp_print_string formatter "0"
    else
      enum vec
      |> Format.fprintf formatter "[@[%a@]]" (SrkUtil.pp_print_enum pp_elt)

  let show = SrkUtil.mk_show pp
  let compare = compare QQ.compare
  let hash = hash (fun (k,v) -> Hashtbl.hash (k, QQ.hash v))
end

module QQMatrix = struct
  include Ring.MakeMatrix(QQ)
  let pp = pp QQ.pp
  let show = SrkUtil.mk_show pp

  let exp m p =
    let one =
      identity (SrkUtil.Int.Set.elements (SrkUtil.Int.Set.union (row_set m) (column_set m)))
    in
    SrkUtil.exp mul one m p

  let rational_eigenvalues m dims =
    if dims = [] then
      []
    else
      let denominator =
        BatEnum.fold (fun d (_, _, entry) ->
            ZZ.lcm d (QQ.denominator entry))
          ZZ.one
          (entries m)
      in
      let dim_array = Array.of_list dims in
      let m =
        Array.map (fun i ->
            Array.map (fun j ->
                let (num, den) = QQ.to_zzfrac (entry i j m) in
                Ntl.ZZ.of_mpz (ZZ.div (ZZ.mul num denominator) den))
              dim_array)
          dim_array
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

let row_eschelon_form mat b_column =
  let rec reduce finished mat =
    if QQMatrix.equal mat QQMatrix.zero then
      finished
    else
      let (row_num, _) = QQMatrix.min_row mat in
      let (next_row, mat') = QQMatrix.pivot row_num mat in
      let column =
        try BatEnum.find (fun (_, i) -> i != b_column) (QQVector.enum next_row) |> snd
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
      reduce ((column,next_row')::finished) (QQMatrix.map_rows f mat')
  in
  reduce [] mat

let nullspace mat dimensions =
  let open QQMatrix in
  let columns = column_set mat in
  let b_column =
    1 + (IntSet.fold max columns (List.fold_left max 0 dimensions))
  in
  let rr = row_eschelon_form mat b_column in
  let rec backprop soln = function
    | [] -> soln
    | ((lhs, rhs)::rest) ->
      backprop (QQVector.add_term (QQVector.dot soln rhs) lhs soln) rest
  in
  let free_dimensions =
    List.filter (fun x ->
        not (List.exists (fun (y, _) -> x = y) rr))
      dimensions
  in
  free_dimensions |> List.map (fun d ->
      let start = QQVector.of_term QQ.one d in
      backprop start rr)

let solve_exn mat b =
  let open QQMatrix in
  logf ~level:`trace "Solving system:@\nM:  %a@\nb:  %a" pp mat QQVector.pp b;
  let columns = column_set mat in
  let b_column = 1 + (IntSet.fold max columns 0) in
  let mat = add_column b_column b mat in
  let rr = row_eschelon_form mat b_column in
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
  logf ~level:`trace "Solution: %a" QQVector.pp res;
  res

let solve mat b =
  try Some (solve_exn mat b)
  with No_solution -> None

let vector_right_mul = QQMatrix.vector_right_mul
let vector_left_mul = QQMatrix.vector_left_mul

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

(* pushout in the category of rational vector spaces.  [pushout A B]
   Consists of a pair of matrices [C] and [D] such that [CA = DB] and
   such that for any other matrices [E] and [F] such that [EA = FB],
   there is a unique [U] such that [UCA = UDB = EA = FB]. *)
let pushout mA mB =
  (* { (c,d) : c*mA = d*mB } is a vector space *)
  (* c*mA = d*mB <==> mA^T c^T = mB^T d^T <==> [mA^T mB^T][ c^T ] = 0
                                                          [ d^T ]      *)
  let module M = QQMatrix in
  let mABt =
    QQMatrix.interlace_columns
      (M.transpose mA)
      (M.transpose (M.scalar_mul (QQ.of_int (-1)) mB))
  in
  let pairs =
    nullspace mABt (IntSet.elements (M.column_set mABt))
  in
  BatList.fold_lefti (fun (mC, mD) i soln ->
      let c, d = QQVector.deinterlace soln in
      (M.add_row i c mC, M.add_row i d mD))
    (M.zero, M.zero)
    pairs

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

let divide_left a b =
  match divide_right (QQMatrix.transpose a) (QQMatrix.transpose b) with
  | Some m -> Some (QQMatrix.transpose m)
  | None -> None

let rational_spectral_decomposition mA dims =
  let mAt = QQMatrix.transpose mA in
  let identity = QQMatrix.identity dims in
  List.fold_left (fun rsd (lambda, multiplicity) ->
      let mE = (* (A^t - lambda*I)^multiplicity *)
        QQMatrix.exp
          (QQMatrix.add mAt (QQMatrix.scalar_mul (QQ.negate lambda) identity))
          multiplicity
      in
      List.fold_left (fun rsd v -> (lambda,v)::rsd) rsd (nullspace mE dims))
    []
    (QQMatrix.rational_eigenvalues mA dims)

let mem_vector_space basis v =
  let mA =
    BatList.fold_lefti
      (fun m i v -> QQMatrix.add_row i v m)
      QQMatrix.zero
      basis
  in
  match solve (QQMatrix.transpose mA) v with
  | Some _ -> true
  | None -> false

let periodic_rational_spectral_decomposition mA dims =
  let nb_dims = List.length dims in
  let max_pow = nb_dims*nb_dims*nb_dims in
  let rec go prsd i mA_pow =
    if i > max_pow || List.length prsd == nb_dims then
      prsd
    else
      let prsd =
        List.fold_left (fun prsd (lambda, v) ->
            if mem_vector_space (List.map (fun (_,_,v) -> v) prsd) v then
              prsd
            else
              (i, lambda, v)::prsd)
          prsd
          (rational_spectral_decomposition mA_pow dims)
      in
      go prsd (i+1) (QQMatrix.mul mA mA_pow)
  in
  go [] 1 mA

let rec jordan_chain mA lambda v =
  let residual = (* v*mA = lambda*v + residual *)
    QQVector.sub
      (QQMatrix.vector_left_mul v mA)
      (QQVector.scalar_mul lambda v)
  in
  if QQVector.is_zero residual then
    [v]
  else
    v::(jordan_chain mA lambda residual)

module QQVectorSpace = struct
  type t = QQVector.t list

  let mem = mem_vector_space

  let empty = []

  let is_empty = (=) []

  let subspace vU vV =
    List.for_all (mem_vector_space vV) vU

  let equal vU vV = subspace vU vV && subspace vV vU

  (* Create a matrix whose rows are a basis for the space *)
  let matrix_of vU =
    BatList.fold_lefti
      (fun m i v -> QQMatrix.add_row i v m)
      QQMatrix.zero
      vU

  let of_matrix mM = BatList.of_enum (QQMatrix.rowsi mM /@ snd)

  let intersect vU vV =
    let (mU, mV) = (matrix_of vU, matrix_of vV) in
    let (mC, _) = intersect_rowspace mU mV in
    of_matrix (QQMatrix.mul mC mU)

  let sum vU vV =
    List.fold_left (fun vR v ->
        if mem vR v then vR
        else v::vR)
      vV
      vU

  let basis vU = sum vU []

  let diff vU vV =
    List.fold_left (fun vR v ->
        if mem (vR @ vV) v then vR
        else v::vR)
      []
      vU

  let standard_basis dim =
    (0 -- (dim - 1))
    /@ QQVector.of_term QQ.one
    |> BatList.of_enum

  let simplify basis =
    let rec go xs ys =
      match ys with
      | (y::ys) ->
        begin match BatEnum.get (QQVector.enum y) with
          | Some (_, dim) ->
            (* Normalize coefficient of dim to 1 *)
            let (coeff, rest) = QQVector.pivot dim y in
            let y =
              QQVector.add_term QQ.one dim (QQVector.scalar_mul (QQ.inverse coeff) rest)
            in
            let reduce x =
              QQVector.add (QQVector.scalar_mul (QQ.negate (QQVector.coeff dim x)) y) x
            in
            go (y::(List.map reduce xs)) (List.map reduce ys)
          | None -> assert false
        end
      | [] -> xs
    in
    go [] basis

  let dimension = List.length
end

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

let term_of_vec srk term_of_dim vec =
  let open QQVector in
  enum vec
  /@ (fun (coeff, dim) ->
      mk_mul srk [mk_real srk coeff; term_of_dim dim])
  |> BatList.of_enum
  |> mk_add srk

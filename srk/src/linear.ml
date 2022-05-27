open Syntax
open BatPervasives

include Log.Make(struct let name = "srk.linear" end)

module IntSet = SrkUtil.Int.Set
module Term = ArithTerm
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

  let split_leading v =
    try
      let (d, b) = min_support v in
      let v' = set d QQ.zero v in
      Some (d, b, v')
    with Not_found ->
      None
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
                Ntl.ZZ.of_mpz (ZZ.mpz_of (ZZ.div (ZZ.mul num denominator) den)))
              dim_array)
          dim_array
      in
      let charpoly = Ntl.ZZMatrix.charpoly m in
      let (_, factors) = Ntl.ZZX.factor charpoly in
      factors |> BatList.filter_map (fun (p, m) ->
                     if Ntl.ZZX.degree p == 1 then
                       (* p = ax + b *)
                       let a = ZZ.of_mpz (Ntl.ZZ.mpz_of (Ntl.ZZX.get_coeff p 1)) in
                       let b = ZZ.of_mpz (Ntl.ZZ.mpz_of (Ntl.ZZX.get_coeff p 0)) in
                       let eigenvalue =
                         QQ.negate (QQ.of_zzfrac b (ZZ.mul a denominator))
                       in
                       Some (eigenvalue, m)
                     else
                       None)
end

exception No_solution

module type SparseArray = sig
  type scalar
  type dim
  type t
  val zero : t
  val split_leading : t -> (dim * scalar * t) option
  val add : t -> t -> t
  val add_term : scalar -> dim -> t -> t
  val scalar_mul : scalar -> t -> t
  val fold : (dim -> scalar -> 'a -> 'a) -> t -> 'a -> 'a
  val pp : Format.formatter -> t -> unit
end

module MakeRewrite
    (K : Algebra.Field)
    (D : Map.OrderedType)
    (V : SparseArray with type dim = D.t
                       and type scalar = K.t) =
struct
  module M = BatMap.Make(D)
  type t = V.t M.t

  let reduce rewrite v =
    let rec go rest v =
      match V.split_leading v with
      | None -> V.add rest v
      | Some (d, a, v') ->
        match M.find_opt d rewrite with
        | Some rhs ->
          go rest (V.add v' (V.scalar_mul (K.negate a) rhs))
        | None ->
          go (V.add_term a d rest) v'
    in
    go V.zero v

  let reducep rewrite v =
    let rec go rest provenance v =
      match V.split_leading v with
      | None -> (V.add rest v, provenance)
      | Some (d, a, v') ->
        match M.find_opt d rewrite with
        | Some rhs ->
          let provenance = V.add_term a d provenance in
          go rest provenance (V.add v' (V.scalar_mul (K.negate a) rhs))
        | None ->
          go (V.add_term a d rest) provenance v'
    in
    go V.zero V.zero v

  let rec reduce_leading rewrite v =
    match V.split_leading v with
    | None -> v
    | Some (d, a, v') ->
      match M.find_opt d rewrite with
      | Some rhs ->
        reduce_leading rewrite (V.add v' (V.scalar_mul (K.negate a) rhs))
      | None -> v

  let add v rewrite =
    let v = reduce_leading rewrite v in
    match V.split_leading v with
    | Some (dim, a, v') ->
      let rhs = V.scalar_mul (K.inverse a) v' in
      `I (M.add dim rhs rewrite)
    | None -> `D v

  let add_drop v rewrite =
    let v = reduce_leading rewrite v in
    match V.split_leading v with
    | Some (dim, a, v') ->
      let rhs = V.scalar_mul (K.inverse a) v' in
      M.add dim rhs rewrite
    | None -> rewrite

  let binding_to_vec (dim, v) = V.add_term K.one dim v
  let basis rewrite = (M.enum rewrite) /@ binding_to_vec
  let rev_basis rewrite = (M.backwards rewrite) /@ binding_to_vec
  let empty = M.empty

  let join x y =
    BatEnum.fold
      (fun rewrite v -> add_drop v rewrite)
      x
      (basis y)

  (* Compute the sum of acc and vec[dim -> transform(dim)] *)
  let rec subst transform acc vec =
    match V.split_leading vec with
    | Some (dim, coeff, vec') ->
      begin
        match M.find_opt dim transform with
        | Some rhs ->
          let acc' = V.add acc (V.scalar_mul coeff rhs) in
          subst transform acc' vec'
        | None -> assert false
      end
    | None -> acc

  let meet rewrite1 rewrite2 =
    let transform =
      M.mapi (fun dim v -> V.add_term K.one dim v) rewrite1
    in
    let (_, _, meet) =
      BatEnum.fold (fun (join, transform, meet) vec ->
          let (vec', provenance) = reducep join vec in
          match V.split_leading vec' with
          | Some (dim, a, v') ->
            let m = K.inverse a in
            let r = subst transform V.zero (V.scalar_mul (K.negate m) provenance) in
            (M.add dim (V.scalar_mul m v') join,
             M.add dim r transform,
             meet)
          | None ->
            (* vec is a linear combination of vectors in rewrite1 and rewrite2.
                 a_1 v_1 + ... + a_n v_n + b_1 u_1 + ... + b_i u_i = vec.
                 So a_1 v_1 + ... + a_n v_n belongs to the intersection *)
            let v = subst transform vec' provenance in
            (join, transform, add_drop v meet))
        (rewrite1, transform, empty)
        (basis rewrite2)
    in
    meet

  let is_leading dim rewrite = M.mem dim rewrite
end

module MakeLinearSpace
    (K : Algebra.Field)
    (D : Map.OrderedType)
    (V : SparseArray with type dim = D.t
                      and type scalar = K.t) =
struct
  module R = MakeRewrite(K)(D)(V)
  type t = R.t
  let zero = R.empty
  let sum = R.join
  let intersect = R.meet
  let is_zero vs = R.M.is_empty vs
  let mem vs v =
    match V.split_leading (R.reduce_leading vs v) with
    | Some _ -> false
    | None -> true
  let dimension vs = R.M.cardinal vs
  let basis = R.basis
  let rev_basis = R.rev_basis
  let is_leading = R.is_leading
  let subspace vs1 vs2 =
    BatEnum.for_all (mem vs2) (basis vs1)
  let equal vs1 vs2 = subspace vs1 vs2 && subspace vs2 vs1
  let add v vs = R.add_drop v vs
  let diff vs1 vs2 =
    BatEnum.fold (fun (diff, sum) v ->
        if mem sum v then (diff, sum)
        else (add v diff, add v sum))
      (zero, vs2)
      (basis vs1)
    |> fst
  let reduce = R.reduce
  let span vectors = BatEnum.fold (fun vs v -> add v vs) zero vectors
end

module MakeLinearMap
    (K : Algebra.Field)
    (D : Map.OrderedType)
    (S : SparseArray with type dim = D.t
                      and type scalar = K.t)
    (T : sig
       type scalar = K.t
       type t
       val zero : t
       val is_zero : t -> bool
       val add : t -> t -> t
       val scalar_mul : scalar -> t -> t
       val pp : Format.formatter -> t -> unit
     end) : sig
  type t
  val empty : t
  val apply : t -> S.t -> T.t option
  val add : S.t -> T.t -> t -> t option
  val add_exn : S.t -> T.t -> t -> t
  val may_add : S.t -> T.t -> t -> t
  val enum : t -> (S.t * T.t) BatEnum.t
  val reverse : t -> (S.t * T.t) BatEnum.t
end = struct
  module R = MakeRewrite(K)(D)(struct
      type t = S.t * T.t
      type scalar = K.t
      type dim = S.dim
      let split_leading (left, right) =
        match S.split_leading left with
        | Some (dim, coeff, left') -> Some (dim, coeff, (left', right))
        | None -> None
      let zero = (S.zero, T.zero)
      let add (left1, right1) (left2, right2) =
        (S.add left1 left2, T.add right1 right2)
      let scalar_mul a (left, right) =
        (S.scalar_mul a left, T.scalar_mul a right)
      let add_term a dim (left, right) = (S.add_term a dim left, right)
      let pp fmt (left, right) =
        Format.fprintf fmt "%a = %a" S.pp left T.pp right
      let fold f (v, _) a = S.fold f v a
    end)
  type t = R.t
  let empty = R.empty
  let neg_one = (K.negate K.one)

  let add src tgt map =
    match R.add (src, T.scalar_mul neg_one tgt) map with
    | `I map' -> Some map'
    | `D (_, tgt) ->
      if T.is_zero tgt then Some map
      else None

  let may_add src tgt map =
    match R.add (src, T.scalar_mul neg_one tgt) map with
    | `I map' -> map'
    | `D (_, _) -> map

  let add_exn src tgt map =
    match add src tgt map with
    | Some map' -> map'
    | None -> invalid_arg "Cannot add binding to linear map: already in domain"

  let apply map vec =
    let (v', result) = R.reduce map (vec, T.zero) in
    match S.split_leading v' with
    | None -> Some result
    | Some _ -> None

  let reverse = R.rev_basis
  let enum = R.basis
end

module QQVS = MakeLinearSpace(QQ)(SrkUtil.Int)(QQVector)

module QQMap = MakeLinearMap(QQ)(SrkUtil.Int)(QQVector)(QQVector)

module QQFun = MakeLinearMap(QQ)(SrkUtil.Int)(QQVector)(struct
    include QQ
    type scalar = QQ.t
    let scalar_mul = QQ.mul
    let is_zero = QQ.equal QQ.zero
  end)


let solve_exn mat b =
  (* Verify that every non-zero row of b is also non-zero in m *)
  QQVector.enum b |> BatEnum.iter (fun (_, d) ->
      if QQVector.is_zero (QQMatrix.row d mat) then
        raise No_solution);

  (* For each row i, map mat_i -> b_i.  If no such map exists, the system is
     inconsistent.  *)
  let rref =
    BatEnum.fold (fun eqs (i, row) ->
        match QQFun.add row (QQ.negate (QQVector.coeff i b)) eqs with
        | Some eqs -> eqs
        | None -> raise No_solution)
      QQFun.empty
      (QQMatrix.rowsi mat)
  in

  (* Back propagate.  Basis takes the form
      [ d_1 + v_1 -> a_1, ..., d_n + v_n -> a_n ]
     where each d_i is the leading term of (d_i + v_i), and
     d_1 < ... < d_n (so if i < j, then d_i doesn't not appear in v_j).
     A solution can be computed as
          r_{n+1} = 0
            r_{i} = r_{i+1} [ d_{i} -> a_{i} - v_{i} . r_{i+1} ]
  *)
  BatEnum.fold (fun soln (v,a) ->
      let (d, b) = QQVector.min_support v in
      assert (QQ.equal b QQ.one);
      let result = QQ.sub a (QQVector.dot soln v) in
      QQVector.add_term result d soln)
    QQVector.zero
    (QQFun.reverse rref)

let solve mat b =
  try Some (solve_exn mat b)
  with No_solution -> None

let solve mat v =
  Log.time "Solve" (solve mat) v

let nullspace mat dimensions =
  let rref =
    BatEnum.fold
      (fun rowspace (_, row) -> QQVS.add row rowspace)
      QQVS.zero
      (QQMatrix.rowsi mat)
  in
  let backprop init =
    BatEnum.fold (fun soln v ->
        let (d, b) = QQVector.min_support v in
        assert (QQ.equal QQ.one b);
        let result = QQ.negate (QQVector.dot soln v) in
        QQVector.add_term result d soln)
      init
      (QQVS.rev_basis rref)
  in
  dimensions
  |> List.filter (fun x -> not (QQVS.is_leading x rref))
  |> List.map (fun d -> backprop (QQVector.of_term QQ.one d))

let vector_right_mul = QQMatrix.vector_right_mul
let vector_left_mul = QQMatrix.vector_left_mul

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
  (* Map the ith row to ith unit vector.  Applying to_row_comb expresses its input
     as a linear combination of the rows of b (if possible) *)
  let to_row_comb =
    BatEnum.fold (fun map (i, row) ->
        QQMap.may_add row (QQVector.of_term QQ.one i) map)
      QQMap.empty
      (QQMatrix.rowsi b)
  in
  SrkUtil.fold_opt (fun div (i, row) ->
      BatOption.map
        (fun soln -> QQMatrix.add_row i soln div)
        (QQMap.apply to_row_comb row))
    QQMatrix.zero
    (QQMatrix.rowsi a)

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

  let vs_of vU =
    BatList.fold_left
      (fun rewrite v -> QQVS.add v rewrite)
      QQVS.zero
      vU

  let of_vs rewrite =
    BatList.of_enum (QQVS.basis rewrite)

  let intersect vU vV =
    let vv = vs_of vV in
    of_vs (QQVS.intersect (vs_of vU) vv)

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

  let scale_integer =
    List.map
      (fun vec ->
        let common_denom =
          (BatEnum.fold
             (fun lcm (coeff, _) -> ZZ.lcm lcm (QQ.denominator coeff))
             ZZ.one
             (QQVector.enum vec))
        in
        QQVector.scalar_mul (QQ.of_zz common_denom) vec)

  let dimension = List.length

  let pp = SrkUtil.pp_print_list QQVector.pp
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
    | `Select _ -> assert false
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

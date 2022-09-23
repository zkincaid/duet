open Normalizffi
open BatPervasives

module L = Log.Make(struct let name = "srk.intLattice" end)

type dim_idx_bijection = { dim_to_idx : int SrkUtil.Int.Map.t
                         ; idx_to_dim : int SrkUtil.Int.Map.t
                         }

let empty_bijection =
  { dim_to_idx = SrkUtil.Int.Map.empty
  ; idx_to_dim = SrkUtil.Int.Map.empty }


module QQEndo = Linear.MakeLinearMap(QQ)(Int)(Linear.QQVector)(Linear.QQVector)

(** A lattice is represented as a matrix 1/[denominator] B,
    where B is in row Hermite normal form and the rows of B are the basis of the
    lattice.
    Each ZZVector.t is viewed as a row vector of B according to [dim_idx_bijection],
    where the smallest dimension (the constant dimension) is in the rightmost
    position of the row/matrix.

    The zero lattice is distinguished because we don't know the dimension of the
    ambient space (and we don't want to call out to Flint).
 *)
type t =
  | ZeroLattice
  | Lattice of { generators: Linear.ZZVector.t list
               ; denominator : ZZ.t
               ; dimensions : SrkUtil.Int.Set.t
               ; inverse : QQEndo.t option ref
               }

let qqify v = Linear.ZZVector.fold (fun dim scalar v ->
                  Linear.QQVector.add_term (QQ.of_zz scalar) dim v)
                v
                Linear.QQVector.zero

let qqify_denom denominator v =
  qqify v |> Linear.QQVector.scalar_mul (QQ.inverse (QQ.of_zz denominator))

let zzify v = Linear.QQVector.fold (fun dim scalar v ->
                  let (num, denom) = (QQ.numerator scalar, QQ.denominator scalar) in
                  if not (ZZ.equal denom ZZ.one) then
                    invalid_arg "IntLattice: zzify: Denominator is not 1"
                  else
                    Linear.ZZVector.add_term num dim v)
                v
                Linear.ZZVector.zero

let fold_matrix
      (rowf : Linear.QQVector.dim -> QQ.t -> 'a -> 'a)
      (row_init : 'a)
      (colf : 'b -> 'a -> 'b)
      (col_init : 'b)
      vectors =
  List.fold_left
    (fun b vec ->
      Linear.QQVector.fold rowf vec row_init |> colf b)
    col_init vectors

let collect_dims_and_lcm_denoms vectors =
  fold_matrix
    (fun dim scalar (dimensions, lcm) ->
      SrkUtil.Int.Set.add dim dimensions, ZZ.lcm lcm (QQ.denominator scalar))
    (SrkUtil.Int.Set.empty, ZZ.one)
    (fun (dims1, lcm1) (dims2, lcm2) ->
      (SrkUtil.Int.Set.union dims1 dims2, ZZ.lcm lcm1 lcm2))
    (SrkUtil.Int.Set.empty, ZZ.one)
    vectors

let collect_dimensions vectors =
  fold_matrix
    (fun dim _scalar dimensions ->
      SrkUtil.Int.Set.add dim dimensions)
    SrkUtil.Int.Set.empty
    SrkUtil.Int.Set.union
    SrkUtil.Int.Set.empty
    vectors

(** Return a bijection between dimensions and (array) indices,
    and the cardinality of dimensions.
    The smallest dimension (ordered by [order]) occurs on the right,
    i.e., gets the largest array index.
*)
let assign_indices order dimensions =
  let dims = SrkUtil.Int.Set.elements dimensions
             |> BatList.sort (fun x y -> -(order x y)) in
  List.fold_left (fun (bij, curr) dim ->
      ({ dim_to_idx = SrkUtil.Int.Map.add dim curr bij.dim_to_idx
       ; idx_to_dim = SrkUtil.Int.Map.add curr dim bij.idx_to_dim
       },
       curr + 1)
    )
    (empty_bijection, 0)
    dims

let densify length dim_to_idx vector =
  Linear.ZZVector.fold (fun dim coeff arr ->
      let idx = SrkUtil.Int.Map.find dim dim_to_idx in
      if idx >= length then
        invalid_arg "densify_and_zzify: index out of bounds"
      else
        begin
          Array.set arr idx (ZZ.mpz_of coeff);
          arr
        end)
    vector
    (Array.make length (Mpzf.of_int 0))

let sparsify idx_to_dim arr =
  Array.fold_left (fun (v, idx) entry ->
      let dim = SrkUtil.Int.Map.find idx idx_to_dim in
      (Linear.ZZVector.add_term entry dim v,
       idx + 1))
    (Linear.ZZVector.zero, 0) arr
  |> fst

(*
   ZZ L = (1/d) ZZ (d L) = (1/d) ZZ B = ZZ (1/d B).
 *)
let dense_hermite_normal_form matrix =
  let level = `trace in
  let verbose = Log.level_leq (!L.my_verbosity_level) level in
  if verbose then Flint.set_debug true else ();
  let mat = Flint.new_matrix matrix in
  Flint.hermitize mat;
  let rank = Flint.rank mat in
  let basis =
    Flint.denom_matrix_of_rational_matrix mat
    |> snd
    |> BatList.take rank (* The rows after rank should be all zeros *)
  in
  if verbose then Flint.set_debug false else ();
  basis

let hermite_normal_form ambient_dimension bijection matrix =
  let densified =
    List.map (Array.to_list % densify ambient_dimension bijection.dim_to_idx) matrix in
  let hermitized = dense_hermite_normal_form densified in
  let generators =
      List.map (Array.of_list % (List.map ZZ.of_mpz)) hermitized
  in
  List.map (sparsify bijection.idx_to_dim) generators

let hermitize vectors =
  if List.for_all (Linear.QQVector.equal Linear.QQVector.zero) vectors
  then ZeroLattice
  else
    let (dimensions, lcm) = collect_dims_and_lcm_denoms vectors in
    let (bijection, length) = assign_indices Int.compare dimensions in
    let generators = hermite_normal_form length bijection
                       (List.map
                          (zzify % Linear.QQVector.scalar_mul (QQ.of_zz lcm))
                          vectors) in
    Lattice
      { generators
      ; denominator = lcm
      ; dimensions
      ; inverse = ref None
      }

let basis t =
  match t with
  | ZeroLattice -> []
  | Lattice { generators ; denominator ; _ } ->
     List.map (qqify_denom denominator) generators

let pp fmt t =
  match t with
  | ZeroLattice -> Format.fprintf fmt "{zero lattice}"
  | Lattice lat ->
     Format.fprintf fmt
       "@[<v 0>
        { denominator: %a@;
        ; basis: %a
        }@]"
       ZZ.pp lat.denominator
       (SrkUtil.pp_print_list Linear.ZZVector.pp) lat.generators

let member v t =
  match t with
  | ZeroLattice -> Linear.QQVector.equal v Linear.QQVector.zero
  | Lattice { generators ; denominator ; inverse ; _ } ->
     let integral v = Linear.QQVector.fold
                        (fun _ scalar bool ->
                          bool && ZZ.equal (QQ.denominator scalar) ZZ.one)
                        v true
     in
     let inv =
       match !inverse with
       | None ->
          let std_vector = Linear.QQVector.of_term QQ.one in
          let (f, _) = List.fold_left (fun (f, idx) g ->
                           let v = qqify_denom denominator g in
                           let f' = QQEndo.add v (std_vector idx) f in
                           match f' with
                           | None -> assert false
                           | Some f' ->
                              (f', idx + 1))
                         (QQEndo.empty, 1) generators
          in f
       | Some inverse -> inverse
     in
     begin
       inverse := Some inv;
       match QQEndo.apply inv v with
       | Some x -> integral x
       | None -> false
     end
     
let project keep t =
  match t with
  | ZeroLattice -> ZeroLattice
  | Lattice { generators ; denominator ; dimensions ; _ } ->
     let new_order x y =
       match keep x, keep y with
       | true, false -> -1
       | false, true -> 1
       | _, _ -> Int.compare x y in
     (* Compute Hermite normal form with unwanted dimensions on the left *)
     let reordered =
       let (bijection, length) = assign_indices new_order dimensions in
       let generators = hermite_normal_form length bijection generators in
       generators
     in
     (* Drop the vectors that have non-zero coefficient in unwanted dimensions *)
     let keep_vector v = Linear.ZZVector.fold
                           (fun dim _scalar drop ->
                             (* scalar should always be non-zero *)
                             drop || not (keep dim))
                           v
                           false in
     let generators = List.filter keep_vector reordered in
     let dimensions = collect_dimensions (List.map qqify generators)
     in
     Lattice {
         generators
       ; denominator
       ; dimensions
       ; inverse = ref None
       }

let project_lower n t =
  match t with
  | ZeroLattice -> ZeroLattice
  | Lattice { generators ; denominator ; dimensions ; _ } ->
     let keep_vector v = Linear.ZZVector.fold
                           (fun dim _scalar drop -> drop || dim > n)
                           v
                           false in
     let generators = List.filter keep_vector generators in
     let dimensions = SrkUtil.Int.Set.filter (fun dim -> dim <= n) dimensions in
     Lattice {
         generators
       ; denominator
       ; dimensions
       ; inverse = ref None
       }

let subset t1 t2 =
  match t1, t2 with
  | ZeroLattice, _ -> true
  | Lattice {generators ; denominator ; _}, t2 ->
     List.for_all (fun g -> member g t2)
       (List.map (qqify_denom denominator) generators)

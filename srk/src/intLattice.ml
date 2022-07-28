open Normalizffi
open BatPervasives

module L = Log.Make(struct let name = "srk.intLattice" end)

type dim_idx_bijection = { dim_to_idx : int SrkUtil.Int.Map.t
                         ; idx_to_dim : int SrkUtil.Int.Map.t
                         }

let pp_bijection fmt bijection =
  Format.fprintf fmt "{ dim_to_idx: @[%a@] }"
    (SrkUtil.pp_print_enum
       (fun fmt (dim, idx) -> Format.fprintf fmt "(dim=%d, idx=%d)" dim idx))
    (SrkUtil.Int.Map.enum bijection.dim_to_idx)

let empty_bijection =
  { dim_to_idx = SrkUtil.Int.Map.empty
  ; idx_to_dim = SrkUtil.Int.Map.empty }

let pp_zz_matrix =
  SrkUtil.pp_print_list
    (fun fmt entry ->
      Format.pp_print_list
        ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
        Mpzf.print fmt entry
    )

(** A lattice is represented as a matrix 1/d B, where B is in row Hermite normal 
    form and the rows of B are the basis of the lattice. In particular, 
    the rows are linearly independent.

    The zero lattice is distinguished because we don't know the dimension of the 
    ambient space (and we don't want to call out to Flint).
 *)
type t =
  | ZeroLattice
  | Lattice of { sparse_rep: Linear.ZZVector.t list
               ; dense_rep: ZZ.t Array.t list
               ; denominator : ZZ.t
               ; dimension_indices : dim_idx_bijection
               }

let qqify v = Linear.ZZVector.fold (fun dim scalar v ->
                  Linear.QQVector.add_term (QQ.of_zz scalar) dim v)
                v
                Linear.QQVector.zero

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

(** Return a bijection between dimensions and (array) indices,
    and the cardinality of dimensions.
    The smallest dimension (ordered by [ordering] occurs on the right, 
    i.e., gets the largest array index.
*)
let assign_indices ordering dimensions =
  let dims = SrkUtil.Int.Set.elements dimensions
             |> BatList.sort (fun x y -> -(ordering x y)) in
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
let hermite_normal_form matrix =
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

let hermitize ?(ordering=Int.compare) vectors =
  if List.for_all (Linear.QQVector.equal Linear.QQVector.zero) vectors
  then ZeroLattice
  else
    let (dimensions, lcm) = collect_dims_and_lcm_denoms vectors in
    let (bijection, length) = assign_indices ordering dimensions in
    let densified = List.map (fun v ->
                        v
                        |> Linear.QQVector.scalar_mul (QQ.of_zz lcm)
                        |> zzify
                        |> densify length bijection.dim_to_idx
                        |> Array.to_list)
                      vectors in
    let hermitized = hermite_normal_form densified in
    let generators =
      List.map (fun xs -> Array.of_list (List.map ZZ.of_mpz xs)) hermitized
    in
    L.logf ~level:`trace "lattice_of: input vectors: @[%a@]@;"
      (SrkUtil.pp_print_list Linear.QQVector.pp) vectors;
    L.logf ~level:`trace "lattice_of: densified: @[%a@]@;"
      pp_zz_matrix densified;
    L.logf ~level:`trace "lattice_of: basis: @[%a@]@;"
      pp_zz_matrix hermitized;
    L.logf ~level:`trace "lattice_of: dimensions-to-indices: @[%a@]@;"
      pp_bijection bijection;
    Lattice
      { sparse_rep = List.map (sparsify bijection.idx_to_dim) generators
      ; dense_rep = generators
      ; denominator = lcm
      ; dimension_indices = bijection
      }

let basis t =
  match t with
  | ZeroLattice -> []
  | Lattice lat ->
     List.map
       (fun v ->
         qqify v
         |> Linear.QQVector.scalar_mul (QQ.inverse (QQ.of_zz lat.denominator)))
       lat.sparse_rep

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
       (SrkUtil.pp_print_list Linear.ZZVector.pp)
       lat.sparse_rep

let member v t =
  match t with
  | ZeroLattice -> Linear.QQVector.equal v Linear.QQVector.zero
  | Lattice lat ->
     let integral v = Linear.QQVector.fold
                        (fun _ scalar bool ->
                          ZZ.equal (QQ.denominator scalar) ZZ.one && bool)
                        v true
     in
     let (matrix, _) =
       List.fold_left (fun (mat, i) vec ->
           let v = qqify vec in
           (Linear.QQMatrix.add_column i v mat, i + 1)
         )
         (Linear.QQMatrix.zero, 0) lat.sparse_rep in
     begin match Linear.solve matrix v with
     | Some x -> integral x
     | None -> false
     end

open Normalizffi
open BatPervasives

module L = Log.Make(struct let name = "srk.intLattice" end)

(* let _ = Log.set_verbosity_level "srk.intLattice" `trace *)

type dim_idx_bijection = { dim_to_idx : int SrkUtil.Int.Map.t
                         ; idx_to_dim : int SrkUtil.Int.Map.t
                         }

let pp_bijection fmt bijection =
  Format.fprintf fmt "{ dim_to_idx: @[%a@] }"
    (SrkUtil.pp_print_enum
       (fun fmt (dim, idx) -> Format.fprintf fmt "(dim=%d, idx=%d)" dim idx))
    (SrkUtil.Int.Map.enum bijection.dim_to_idx)

let pp_zz_matrix =
  SrkUtil.pp_print_list
    (fun fmt entry ->
      Format.pp_print_list
        ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
        Mpzf.print fmt entry
    )

(** A lattice is represented as a matrix 1/d B,
    where B is in row Hermite normal form
    and the rows of B are the basis of the lattice.
    In particular, the rows are linearly independent.

    The empty lattice is distinguished because we don't want to call out
    to Flint for empty lattices.
 *)
type t =
  | EmptyLattice
  | Lattice of { sparse_rep: Linear.ZZVector.t list
               ; dense_rep: ZZ.t Array.t list
               ; denominator : ZZ.t
               ; dimension_indices : dim_idx_bijection
               }

let empty_dim_idx_bijection =
  { dim_to_idx = SrkUtil.Int.Map.empty
  ; idx_to_dim = SrkUtil.Int.Map.empty }

let dims_and_lcm_denoms vectors =
  let dims_and_lcm_denoms' v =
    BatEnum.fold (fun (dimensions, lcm) (q, dim) ->
        (SrkUtil.Int.Set.add dim dimensions, ZZ.lcm lcm (QQ.denominator q)))
      (SrkUtil.Int.Set.empty, ZZ.of_int 1)
      (Linear.QQVector.enum v)
  in
  List.fold_left
    (fun (dimensions, lcm) v -> let (dims, m) = dims_and_lcm_denoms' v in
                                (SrkUtil.Int.Set.union dimensions dims, ZZ.lcm lcm m))
    (SrkUtil.Int.Set.empty, ZZ.one)
    vectors

(** Return a bijection between dimensions and (array) indices,
    and the cardinality of dimensions.
*)
let assign_indices ordering dimensions =
  let dims = SrkUtil.Int.Set.elements dimensions |> BatList.sort ordering in
  List.fold_left (fun (bij, curr) dim ->
      ({ dim_to_idx = SrkUtil.Int.Map.add dim curr bij.dim_to_idx
       ; idx_to_dim = SrkUtil.Int.Map.add curr dim bij.idx_to_dim
       },
       curr + 1)
    )
    (empty_dim_idx_bijection, 0)
    dims

let densify_and_zzify length dim_to_idx denom_to_clear vector =
  BatEnum.fold
    (fun arr (coeff, dim) ->
      let q = QQ.mul coeff (QQ.of_zz denom_to_clear) in
      if ZZ.equal (QQ.denominator q) ZZ.one then
        begin
          let idx = SrkUtil.Int.Map.find dim dim_to_idx in
          if idx >= length then
            invalid_arg "densify_and_zzify: index out of bounds"
          else
            begin
              Array.set arr idx (ZZ.mpz_of (QQ.numerator q));
              arr
            end
        end
      else
        invalid_arg "densify_and_zzify: argument supplied does not clear denominator")
    (Array.make length (Mpzf.of_int 0))
    (Linear.QQVector.enum vector)

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
  let verbose =
    if
      (* Log.level_leq (!Log.verbosity_level) level || *)
      Log.level_leq (!L.my_verbosity_level) level
    then true else false in
  if verbose then Flint.set_debug true else ();
  let mat = Flint.new_matrix matrix in
  L.logf ~level "hermite_normal_form: testing new matrix@;";
  let (denom, m) =  Flint.denom_matrix_of_rational_matrix mat in
  L.logf ~level "hermite_normal_form: new matrix: @[denom: %a@;matrix: %a@]"
    Mpzf.print denom
    pp_zz_matrix m;

  Flint.hermitize mat;
  let rank = Flint.rank mat in
  let basis =
    Flint.denom_matrix_of_rational_matrix mat
    |> snd
    |> BatList.take rank (* The rows after rank should be all zeros *)
  in
  if verbose then Flint.set_debug false else ();
  basis

let rev_compare x y = - Int.compare x y

let lattice_of ?(ordering=rev_compare) vectors =
  if List.for_all (Linear.QQVector.equal Linear.QQVector.zero) vectors
  then EmptyLattice
  else
    let (dimensions, lcm) = dims_and_lcm_denoms vectors in
    let (bijection, length) = assign_indices ordering dimensions in
    let densified = List.map (fun v ->
                        v
                        |> densify_and_zzify length bijection.dim_to_idx lcm
                        |> Array.to_list)
                      vectors in
    let hermitized = hermite_normal_form densified in
    let generators =
      List.map (fun xs -> Array.of_list (List.map ZZ.of_mpz xs)) hermitized
    in
    L.logf "lattice_of: input vectors: @[%a@]@;"
      (SrkUtil.pp_print_list Linear.QQVector.pp) vectors;
    L.logf ~level:`trace "lattice_of: densified: @[%a@]@;"
      pp_zz_matrix densified;
    L.logf "lattice_of: basis: @[%a@]@;"
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
  | EmptyLattice -> (ZZ.one, [])
  | Lattice lat -> (lat.denominator, lat.sparse_rep)

let pp fmt t =
  match t with
  | EmptyLattice -> Format.fprintf fmt "{empty lattice}"
  | Lattice lat ->
     Format.fprintf fmt
       "@[<v 0>
        { denominator: %a@;
        ; basis: %a 
        }@]"
       ZZ.pp lat.denominator
       (SrkUtil.pp_print_list Linear.ZZVector.pp)
       lat.sparse_rep

(*
let pp_term pp_dim fmt t =
  match t with
  | EmptyLattice -> Format.fprintf fmt "{empty lattice}"
  | Lattice lat ->
     Format.fprintf fmt
       "{denominator: %a; basis: %a}"
       ZZ.pp lat.denominator
       (Format.pp_print_list ~pp_sep:Format.pp_print_cut
          (Linear.ZZVector.pp_term pp_dim))
       lat.sparse_rep
 *)

let _flint_member v t =
  match t with
  | EmptyLattice -> false
  | Lattice lat ->
     let embedding_dim = Array.length (List.hd lat.dense_rep) in
     let mat =
       List.map (fun row -> List.map ZZ.mpz_of (Array.to_list row)) lat.dense_rep
       |> Flint.new_matrix
     in
     (* The generators should be linearly independent *)
     let rank = List.length lat.dense_rep in
     let extended_basis = Flint.extend_hnf_to_basis mat in
     let transposed = Flint.transpose extended_basis in
     let inv = Flint.matrix_inverse transposed in
     let vec = densify_and_zzify embedding_dim lat.dimension_indices.dim_to_idx
                 ZZ.one v
               |> (fun arr -> Flint.new_matrix [Array.to_list arr])
               |> Flint.transpose in
     let (denom, preimage) = Flint.matrix_multiply inv vec
                             |> Flint.denom_matrix_of_rational_matrix in
     let preimage_vector = List.concat preimage in
     let (prefix, suffix) = BatList.takedrop rank preimage_vector in
     (* The unique solution to B^T y = v must have all zeroes in the extended
        part of the basis to fall within the QQ-span of the lattice,
        and then have ZZ entries to be within the ZZ-span of the lattice.
      *)
     let (transposed_denom, transposed_matrix) =
       Flint.denom_matrix_of_rational_matrix transposed in
     let (target_denom, target_vector) = Flint.denom_matrix_of_rational_matrix vec in
     L.logf
       "@[<v 0>Lattice: %a
        @; embedding dimension: %d | rank: %d
        @; Transposed: (1/%a) %a
        @; v in B^T x = v: (1/%a) %a
        @; Preimage: %a
        @]"
       pp t
       embedding_dim
       rank
       Mpzf.print transposed_denom
       pp_zz_matrix transposed_matrix
       Mpzf.print target_denom
       pp_zz_matrix target_vector
       pp_zz_matrix preimage;
     (List.for_all (fun x -> Mpzf.cmp_int x 0 = 0) suffix)
     && (List.for_all (fun x -> Mpzf.cmp_int (Mpzf.fdiv_r x denom) 0 = 0) prefix)

let member v t =
  match t with
  | EmptyLattice -> false
  | Lattice lat ->
     let (matrix, _) =
       List.fold_left (fun (mat, i) vec ->
           let v = Linear.ZZVector.fold (fun dim scalar v ->
                       Linear.QQVector.add_term (QQ.of_zz scalar) dim v)
                     vec
                     Linear.QQVector.zero in
           (Linear.QQMatrix.add_column i v mat, i + 1)
         )
         (Linear.QQMatrix.zero, 0) lat.sparse_rep in
     begin match Linear.solve matrix v with
     | Some x -> (Linear.QQVector.fold
                    (fun _ scalar bool ->
                      ZZ.equal (QQ.denominator scalar) ZZ.one && bool)
                    x)
                   true
     | None -> false
     end

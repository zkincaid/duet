open Normalizffi
open BatPervasives

module L = Log.Make(struct let name = "srk.intLattice" end)

module D = Linear.MakeDenseConversion(SrkUtil.Int)(Linear.QQVector)

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
               ; dimension_indices : D.context
               }

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

let make_context dimensions = D.make_context (SrkUtil.Int.Set.elements dimensions)

let densify_and_zzify ctx denom_to_clear vector =
  let arr = Array.make (D.dim ctx) (Mpzf.of_int 0) in
  BatEnum.iter
    (fun (coeff, dim) ->
       match QQ.to_zz (QQ.mul coeff (QQ.of_zz denom_to_clear)) with
       | Some zz -> arr.(D.int_of_dim ctx dim) <- ZZ.mpz_of zz
       | None -> invalid_arg "densify_and_zzify: argument supplied does not \
                              clear denominator")
    (Linear.QQVector.enum vector);
  arr

let sparsify ctx arr =
  BatArray.fold_lefti (fun v i entry ->
      Linear.ZZVector.add_term entry (D.dim_of_int ctx i) v)
    Linear.ZZVector.zero
    arr

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

let lattice_of vectors =
  if List.for_all (Linear.QQVector.equal Linear.QQVector.zero) vectors
  then EmptyLattice
  else
    let (dimensions, lcm) = dims_and_lcm_denoms vectors in
    let ctx = make_context dimensions in
    let densified = List.map (fun v ->
                        v
                        |> densify_and_zzify ctx lcm
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
      (D.pp Format.pp_print_int) ctx;
    Lattice
      { sparse_rep = List.map (sparsify ctx) generators
      ; dense_rep = generators
      ; denominator = lcm
      ; dimension_indices = ctx
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
     let vec = densify_and_zzify lat.dimension_indices ZZ.one v
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

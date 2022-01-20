
open Normalizffi

type dim_idx_bijection = { dim_to_idx : int SrkUtil.Int.Map.t
                         ; idx_to_dim : int SrkUtil.Int.Map.t
                         }

(** A lattice is represented as a matrix 1/d B,
    where B is in a row Hermite normal form
    and the rows of B are the generators of the lattice.
 *)
type t = { sparse_rep: Linear.ZZVector.t list
         ; dense_rep: ZZ.t Array.t list
         ; denominator : ZZ.t
         ; dimension_indices : dim_idx_bijection
         }

module L = Log.Make(struct let name = "intLattice" end)

let dims_and_lcm_denoms vectors =
  let dims_and_lcm_denoms' v =
    BatEnum.fold (fun (dimensions, lcm) (q, dim) ->
        (SrkUtil.Int.Set.add dim dimensions, ZZ.lcm lcm (QQ.denominator q)))
      (SrkUtil.Int.Set.empty, Mpzf.of_int 1)
      (Linear.QQVector.enum v)
  in
  List.fold_left
    (fun (dimensions, lcm) v -> let (dims, m) = dims_and_lcm_denoms' v in
                                (SrkUtil.Int.Set.union dimensions dims, ZZ.lcm lcm m))
    (SrkUtil.Int.Set.empty, ZZ.one)
    vectors

(* Return a bijection between dimensions and (array) indices,
   and the cardinality of dimensions.
*)
let assign_indices dimensions =
  SrkUtil.Int.Set.fold (fun dim (bij, curr) ->
      ({ dim_to_idx = SrkUtil.Int.Map.add dim curr bij.dim_to_idx
       ; idx_to_dim = SrkUtil.Int.Map.add curr dim bij.idx_to_dim
       },
       curr + 1)
    )
    dimensions
    ({ dim_to_idx = SrkUtil.Int.Map.empty
     ; idx_to_dim = SrkUtil.Int.Map.empty },
     0)

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
              Array.set arr idx (QQ.numerator q);
              arr
            end
        end
      else
        invalid_arg "densify_and_zzify: argument supplied does not clear denominator")
    (Array.make length ZZ.zero)
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
  let mat = Flint.new_matrix matrix in
  Flint.hermitize mat;
  Flint.zz_matrix_of_matrix mat

let lattice_of vectors =
  let (dimensions, lcm) = dims_and_lcm_denoms vectors in
  let (bijection, length) = assign_indices dimensions in
  let generators = List.map (fun v ->
                       v
                       |> densify_and_zzify length bijection.dim_to_idx lcm
                       |> Array.to_list)
                     vectors
                   |> hermite_normal_form
                   |> List.map Array.of_list
  in
  { sparse_rep = List.map (sparsify bijection.idx_to_dim) generators
  ; dense_rep = generators
  ; denominator = lcm
  ; dimension_indices = bijection
  }

let basis t = (t.denominator, t.sparse_rep)

let pp fmt t =
  Format.fprintf fmt
    "@[<v 0>{denominator: %a; @[basis: %a@]}@]"
    ZZ.pp t.denominator
    (Format.pp_print_list ~pp_sep:Format.pp_print_cut
       Linear.ZZVector.pp)
    t.sparse_rep

let pp_term pp_dim fmt t =
  Format.fprintf fmt
    "@[<v 0>{denominator: %a; @[basis: %a@]}@]"
    ZZ.pp t.denominator
    (Format.pp_print_list ~pp_sep:Format.pp_print_cut
       (Linear.ZZVector.pp_term pp_dim))
    t.sparse_rep

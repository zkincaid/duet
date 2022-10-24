open Polynomial
open BatPervasives

module L = Log.Make(struct let name = "srk.polyLattice" end)

(** Affine lattice is reduced with respect to ideal.
    The lattice is unchanged whether the affine lattice is reduced or not.
 *)
type t =
  { ideal : Ideal.t
  ; affine_lattice : IntLattice.t
  ; affine_context : LinearQQXs.context
  }

let make_context monomial_order polys =
  let module MonomialSet =
    BatSet.Make(struct type t = Monomial.t
                       let compare x y = match monomial_order x y with
                         | `Lt -> -1
                         | `Eq -> 0
                         | `Gt -> 1
                end)
  in
  let sorted_monos =
    polys
    |> List.fold_left
         (fun monos poly ->
           QQXs.enum poly
           |> BatEnum.fold (fun s (_coeff, mono) -> MonomialSet.add mono s)
                monos)
         MonomialSet.empty
    |> MonomialSet.elements
  in
  (LinearQQXs.make_context sorted_monos, sorted_monos)

let ideal t = t.ideal
  
let affine_basis t =
  List.map (LinearQQXs.sparsify_affine t.affine_context)
    (IntLattice.basis t.affine_lattice)

let pp pp_dim fmt t =
  Format.fprintf fmt
    "{ affine_basis: @[<v 0>%a@]@;
       ideal: @[<v 0>%a@]
     }"
    (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "; ")
       (QQXs.pp pp_dim)) (affine_basis t)
    (Ideal.pp pp_dim) (ideal t)

let reduce red polys =
  BatList.filter_map
    (fun p -> let p' = red p in
              if QQXs.equal p' QQXs.zero then None
              else Some p')
    polys

let make ideal affine_polys : t =
  let pp_dim = (fun fmt dim -> Format.fprintf fmt "%d" dim) in 
  L.logf ~level:`always
    "PolynomialLattice: of ideal @[%a@] and affine polynomials @[%a@]@;"
    (Ideal.pp pp_dim) ideal
    (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "; ")
       (QQXs.pp pp_dim))
    affine_polys;
  let ideal = ideal in
  let affine_polys = reduce (Ideal.reduce ideal) affine_polys in
  let affine_context = LinearQQXs.min_context (BatList.enum affine_polys) in
  let vectors = List.map (LinearQQXs.densify_affine affine_context)
                  affine_polys in
  let affine_lattice = IntLattice.hermitize vectors in
  { ideal ; affine_lattice ; affine_context }

let member poly t =
  try
    Ideal.reduce (ideal t) poly
    |> (fun p -> IntLattice.member
                   (LinearQQXs.densify_affine t.affine_context p)
                   t.affine_lattice)
  with Linear.Not_in_context ->
    (* TODO: Suggest moving this exception into Linear.DenseConversion *)
    false

let sum t1 t2 =
  let ideal = Ideal.sum (ideal t1) (ideal t2) in
  let affine = (affine_basis t1) @ (affine_basis t2) in
  make ideal affine

let fresh_dim polys =
  let fresh =
    List.fold_left
      (fun curr_fresh poly ->
        QQXs.dimensions poly
        |> SrkUtil.Int.Set.max_elt_opt
        |> (fun d ->
         match d with
         | Some d ->
            Int.max curr_fresh (d + 1)
         | None -> curr_fresh))
      Linear.const_dim
      polys in
  if fresh < 0 then 0 else fresh

let intersect t1 t2 =
  let ideal1, ideal2 = Ideal.generators (ideal t1), Ideal.generators (ideal t2) in
  let affine1, affine2 = affine_basis t1, affine_basis t2 in
  let all_polys = List.concat [ ideal1 ; ideal2 ; affine1 ; affine2 ] in
  if all_polys = []
  then make (Ideal.make []) []
  else
    let fresh = fresh_dim all_polys in
    let elim_order = Monomial.block [fun dim -> dim = fresh] Monomial.degrevlex in
    let w = QQXs.of_dim fresh in
    let w' = QQXs.sub QQXs.one w in
    let weight w polys = List.map (QQXs.mul w) polys in
    let weighted_ideal1, weighted_ideal2 = (weight w ideal1, weight w' ideal2) in
    let weighted_affine1, weighted_affine2 = (weight w affine1, weight w' affine2) in
    let weighted_ideal = Rewrite.mk_rewrite elim_order (weighted_ideal1 @ weighted_ideal2) in
    let weighted_affine = reduce (Rewrite.reduce weighted_ideal)
                            (weighted_affine1 @ weighted_affine2) in
    let (affine_context, sorted_monos) = make_context elim_order weighted_affine in
    let cutoff_dim =
      try
        let (idx, _) = BatList.findi (fun _idx mono -> Monomial.power fresh mono > 0)
                         sorted_monos
        in Some idx
      with Not_found ->
        None
    in
    let affine_lattice =
      List.map (LinearQQXs.densify_affine affine_context) weighted_affine
      |> IntLattice.hermitize
      |> (fun lattice ->
        match cutoff_dim with
        | None -> lattice
        | Some cutoff ->
           IntLattice.project_lower (cutoff - 1) lattice)
    in
    let projected_ideal =
      Rewrite.restrict
        (fun m -> BatEnum.for_all (fun (dim, _pow) -> dim <> fresh)
                    (Monomial.enum m))
        weighted_ideal
    in
    (* TODO: The affine lattice should not need to be reduced by projected_ideal
       because all monomials in the affine lattice are not reducible by
       the original ideal. Verify that's true.
     *)
    { ideal = Ideal.make (Rewrite.generators projected_ideal)
    ; affine_lattice
    ; affine_context
    }

let subset t1 t2 =
  List.for_all (fun p -> member p t2) (affine_basis t1)
  && List.for_all (fun p -> (QQXs.equal (Ideal.reduce (ideal t2) p)) QQXs.zero)
       (Ideal.generators (ideal t1))

let equal t1 t2 = subset t1 t2 && subset t2 t1

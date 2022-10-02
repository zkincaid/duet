open Polynomial

module L = Log.Make(struct let name = "srk.polyLattice" end)

(** Affine lattice is reduced with respect to ideal.
    The lattice is unchanged whether the affine lattice is reduced or not.
 *)
type t =
  { ideal : Rewrite.t
  ; affine_lattice : IntLattice.t
  ; affine_context : LinearQQXs.context
  }

(* Some graded order *)
let monomial_order = Polynomial.Monomial.degrevlex

module MonomialSet =
  BatSet.Make(struct type t = Monomial.t
                     let compare x y = match Monomial.degrevlex x y with
                       | `Lt -> -1
                       | `Eq -> 0
                       | `Gt -> 1
              end)

(* TODO: Check if we can disregard monomial order and just use [min_context].
   In projection, we need monomials weighted with fresh dimensions/variables
   to occur as higher dimensions when densifying into vectors for integer
   lattice projection.
 *)
let make_context polys =
  let monos = List.fold_left
                (fun monos poly ->
                  BatEnum.fold (fun s (_coeff, mono) -> MonomialSet.add mono s)
                    monos (QQXs.enum poly))
                MonomialSet.empty polys
  in
  LinearQQXs.make_context (MonomialSet.elements monos)

(*
let zero =
  { ideal = Rewrite.mk_rewrite monomial_order []
  ; affine_lattice = IntLattice.hermitize []
  ; affine_context = LinearQQXs.min_context (BatList.enum [])
  }
 *)

let ideal t = t.ideal

let affine_basis t =
  List.map (LinearQQXs.sparsify_affine t.affine_context) (IntLattice.basis t.affine_lattice)

let pp pp_dim fmt t =
  Format.fprintf fmt
    "{ affine_basis: @[<v 0>%a@]@;
       ideal: @[<v 0>%a@]
     }"
    (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "; ")
       (QQXs.pp pp_dim))
    (List.map (LinearQQXs.sparsify t.affine_context) (IntLattice.basis t.affine_lattice))
    (Rewrite.pp pp_dim) t.ideal

let reduce ideal polys =
  BatList.filter_map
    (fun p -> let p' = Rewrite.reduce ideal p in
              if QQXs.equal p' QQXs.zero then None
              else Some p')
    polys

let make ideal affine_polys : t =
  let ideal = Rewrite.mk_rewrite monomial_order (Ideal.generators ideal) in
  let affine_polys = reduce ideal affine_polys in
  let affine_context = make_context affine_polys in
  let vectors = List.map (LinearQQXs.densify_affine affine_context)
                  affine_polys in
  let affine_lattice = IntLattice.hermitize vectors in
  { ideal ; affine_lattice ; affine_context }

let member poly t =
  try
    Rewrite.reduce t.ideal poly
    |> (fun p -> IntLattice.member (LinearQQXs.densify_affine t.affine_context p)
                   t.affine_lattice)
  with Linear.Not_in_context ->
    (* TODO: Suggest moving this exception into Linear.DenseConversion *)
    false

let sum t1 t2 =
  let ideal1, ideal2 = ideal t1, ideal t2 in
  let ideal =
    List.append (Rewrite.generators ideal1) (Rewrite.generators ideal2)
    |> Ideal.make
  in
  let affine = List.append (affine_basis t1) (affine_basis t2) in
  make ideal affine

(*
let variable_in_monomial dim mono =
  BatEnum.fold (fun seen (d, _pow) -> seen || d = dim) false (Monomial.enum mono)

let first_dim_containing_variable variable ctxt =
  BatEnum.fold
    (function
     | None ->
        (fun (dim, mono) ->
          if variable_in_monomial variable mono then Some dim
          else None)
     | Some d -> fun _ -> Some d)
    None
    (PolyVectorContext.enum_by_dimension ctxt)

let intersect t1 t2 =
  let ideal1, ideal2 = Rewrite.generators (ideal t1), Rewrite.generators (ideal t2) in
  let affine1, affine2 = affine_basis t1, affine_basis t2 in
  let all_polys = List.concat [ ideal1 ; ideal2 ; affine1 ; affine2 ] in
  if all_polys = []
  then zero
  else
    let fresh = List.fold_left
                  (fun dims poly -> SrkUtil.Int.Set.union dims (QQXs.dimensions poly))
                  SrkUtil.Int.Set.empty
                  (List.concat [ideal1 ; ideal2 ; affine1 ; affine2])
                |> (fun dims -> SrkUtil.Int.Set.max_elt dims + 1) in
    let elim_order = Monomial.block [fun dim -> dim = fresh] monomial_order in
    let w = QQXs.of_dim fresh in
    let w' = QQXs.sub QQXs.one w in
    let weight w polys = List.map (QQXs.mul w) polys in
    let weighted_ideal1, weighted_ideal2 = (weight w ideal1, weight w' ideal2) in
    let weighted_affine1, weighted_affine2 = (weight w affine1, weight w' affine2) in
    let weighted_ideal =
      Rewrite.mk_rewrite elim_order (List.append weighted_ideal1 weighted_ideal2) in
    let weighted_affine = reduce weighted_ideal
                            (List.append weighted_affine1 weighted_affine2) in
    let affine_context =
      PolyVectorContext.mk_context ~increasing:true elim_order weighted_affine in
    let affine_lattice =
      List.map (LinearQQXs.densify_affine affine_context) weighted_affine
      |> IntLattice.hermitize
      |> (fun lattice ->
        match first_dim_containing_variable fresh affine_context with
        | None -> lattice
        | Some cutoff ->
           IntLattice.project_lower (cutoff - 1) lattice)
    in
    let projected_ideal =
      Rewrite.generators weighted_ideal
      |> List.filter (fun p -> not (SrkUtil.Int.Set.mem fresh (QQXs.dimensions p)))
      |> Rewrite.mk_rewrite monomial_order in
    (* TODO: The affine lattice should not need to be reduced by projected_ideal
       because all monomials in the affine lattice are not reducible by
       the original ideal. Verify that's true.
     *)
    { ideal = projected_ideal
    ; affine_lattice
    ; affine_context
    }
 *)

let subset t1 t2 =
  let aff1 = affine_basis t1 in
  let ideal1 = ideal t1 in
  let polys1 = List.append (Rewrite.generators ideal1) aff1 in
  List.for_all (fun p -> member p t2) polys1

let equal t1 t2 = subset t1 t2 && subset t2 t1

open Polynomial
open BatPervasives

module L = Log.Make(struct let name = "srk.polyLattice" end)

(** Affine lattice is reduced with respect to ideal.
    The lattice is unchanged whether the affine lattice is reduced or not.
 *)
type t =
  { ideal : Rewrite.t
  ; affine_lattice : IntLattice.hnf IntLattice.t
  (* Maps lowest monomial per ideal's monomial order to least integer dimension *)
  ; affine_context : LinearQQXs.context
  }

let default_order = Monomial.degrevlex

let monomials monomial_order polys =
  let module MonomialSet =
    BatSet.Make(
      struct
        type t = Monomial.t
          let compare x y =
            match monomial_order x y with
            | `Lt -> -1
            | `Eq -> 0
            | `Gt -> 1
      end
    )
  in
  polys
  |> List.fold_left
       (fun monos poly ->
         QQXs.enum poly
         |> BatEnum.fold (fun s (_coeff, mono) -> MonomialSet.add mono s)
              monos)
       MonomialSet.empty
  |> MonomialSet.elements

let make_context monomial_order polys =
  LinearQQXs.make_context (monomials monomial_order polys)

let affine_basis t =
  List.map (LinearQQXs.sparsify_affine t.affine_context)
    (IntLattice.generators t.affine_lattice)

let pp pp_dim fmt t =
  Format.fprintf fmt
    "{ affine_basis: @[<v 0>%a@]@;
       ideal: @[<v 0>%a@]
     }"
    (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "; ")
       (QQXs.pp pp_dim)) (affine_basis t)
    (Rewrite.pp pp_dim) t.ideal

let reduce red polys =
  BatList.filter_map
    (fun p -> let p' = red p in
      if QQXs.equal p' QQXs.zero then None
      else Some p')
    polys

let make_lattice ideal affine_polys : t =
  let affine_polys = reduce (Rewrite.reduce ideal) affine_polys in
  let order = Rewrite.get_monomial_ordering ideal in
  let affine_context = make_context order affine_polys in
  let vectors = List.map (LinearQQXs.densify_affine affine_context)
      affine_polys in
  let affine_lattice = IntLattice.of_generators vectors |> IntLattice.hermitize in
  { ideal ; affine_lattice ; affine_context }

let change_monomial_ordering t order =
  make_lattice (Rewrite.reorder_groebner order t.ideal) (affine_basis t)

let member poly t =
  try
    Rewrite.reduce t.ideal poly
    |> (fun p -> IntLattice.member
           (LinearQQXs.densify_affine t.affine_context p)
           t.affine_lattice)
  with Linear.Not_in_context ->
    (* TODO: Suggest moving this exception into Linear.DenseConversion *)
    false

let sum t1 t2 =
  let ideal =  (Rewrite.generators t1.ideal) @ (Rewrite.generators t2.ideal)
               |> Rewrite.mk_rewrite default_order
  in
  let affine = (affine_basis t1) @ (affine_basis t2) in
  make_lattice ideal affine

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

(* TODO: Extend DenseConversion to support restriction? *)
let copy_context_up_to n context =
  BatEnum.fold (fun lst i -> LinearQQXs.dim_of_int context i :: lst) [] (n --- 0)
  |> LinearQQXs.make_context

let restrict p t =
  let max_retained =
    BatEnum.find (fun i -> p (LinearQQXs.dim_of_int t.affine_context i))
      (LinearQQXs.dim t.affine_context --- 0)
  in
  let affine_lattice =
    IntLattice.project_as_dual ~keep:(fun dim -> dim <= max_retained)
      t.affine_lattice in
  { ideal = Rewrite.restrict p t.ideal
  ; affine_lattice
  ; affine_context = copy_context_up_to max_retained t.affine_context
  }

let intersect t1 t2 =
  let ideal1, ideal2 = Rewrite.generators t1.ideal, Rewrite.generators t2.ideal in
  let affine1, affine2 = affine_basis t1, affine_basis t2 in
  let all_polys = List.concat [ ideal1 ; ideal2 ; affine1 ; affine2 ] in
  if all_polys = []
  then make_lattice (Rewrite.mk_rewrite default_order []) []
  else
    let fresh = fresh_dim all_polys in
    let elim_order = Monomial.block [fun dim -> dim = fresh] Monomial.degrevlex in
    let w = QQXs.of_dim fresh in
    let w' = QQXs.sub QQXs.one w in
    let weight w polys = List.map (QQXs.mul w) polys in
    let weighted_ideal1, weighted_ideal2 = (weight w ideal1, weight w' ideal2) in
    let weighted_affine1, weighted_affine2 = (weight w affine1, weight w' affine2) in
    let weighted_ideal = Rewrite.mk_rewrite elim_order (weighted_ideal1 @ weighted_ideal2) in
    let t = make_lattice weighted_ideal (weighted_affine1 @ weighted_affine2) in
    let pred mono = (elim_order mono (Monomial.singleton fresh 1) = `Lt) in
    restrict pred t

let subset t1 t2 =
  List.for_all (fun p -> member p t2) (affine_basis t1)
  && List.for_all (fun p -> (QQXs.equal (Rewrite.reduce t2.ideal p)) QQXs.zero)
    (Rewrite.generators t1.ideal)

let equal t1 t2 = subset t1 t2 && subset t2 t1

open BatPervasives
open Polynomial

type t = Rewrite.t

let use_msolve = ref true

let order = Monomial.degrevlex

let nonzero polynomials =
  List.filter (fun polynomial -> not (QQXs.is_zero polynomial)) polynomials

let variables polynomials =
  let module IS = SrkUtil.Int.Set in
  List.fold_left
    (fun variables polynomial -> IS.union variables (QQXs.dimensions polynomial))
    IS.empty
    polynomials

(* For small instances, the overhead of launching msolve dominates
   Groebner basis computation time.  This function heursitically
   detects small instances. *)
let is_small_instance generators =
  let max_quadrics = 4 in
  let degree_at_most d = List.for_all (fun p -> QQXs.degree p <= d) in
  degree_at_most 1 generators
  || (List.compare_length_with generators max_quadrics <= 0
      && degree_at_most 2 generators)

let use_msolve_for generators =
  !use_msolve
  && not (is_small_instance generators)
  && Msolve.available ()

let rewrite_of_basis basis =
  Rewrite.mk_rewrite order basis
  |> Rewrite.reduce_rewrite

let make_buchberger generators =
  Rewrite.grobner_basis (Rewrite.mk_rewrite order generators)

let make generators =
  let generators = nonzero generators in
  if generators = [] then Rewrite.mk_rewrite order []
  else if use_msolve_for generators then
    let variables = variables generators in
    if SrkUtil.Int.Set.is_empty variables then make_buchberger generators
    else
      (* msolve gives variables at the beginning of its list higher
         precedence.  SRK's [degrevlex] gives higher-numbered dimensions
         higher precedence, so reverse the increasing dimension list. *)
      let block = SrkUtil.Int.Set.elements variables in
      Msolve.grobner_basis (List.rev block) [] generators
      |> rewrite_of_basis
  else
    make_buchberger generators

let add_saturate ideal polynomial =
  if QQXs.is_zero polynomial then ideal
  else if use_msolve_for (polynomial :: Rewrite.generators ideal) then
    make (polynomial :: Rewrite.generators ideal)
  else Rewrite.add_saturate ideal polynomial

let reduce = Rewrite.reduce

let generators = Rewrite.generators

let pp = Rewrite.pp

let subset = Rewrite.subset

let equal = Rewrite.equal

let mem polynomial ideal =
  Rewrite.reduce_zero ideal polynomial

let project_generators pred generators =
  let module IS = SrkUtil.Int.Set in
  let bad, good =
    variables generators
    |> IS.partition (not % pred)
  in
  if IS.is_empty bad then make generators
  else if use_msolve_for generators then
    (* Reverse both blocks for the same variable-precedence convention used
       in [make].  The first block remains the elimination block. *)
    Msolve.eliminate
      (List.rev (IS.elements bad))
      (List.rev (IS.elements good))
      generators
    |> make
  else
    let elim_order = Monomial.block [not % pred] order in
    Rewrite.mk_rewrite elim_order generators
    |> Rewrite.grobner_basis
    |> Rewrite.restrict
         (fun monomial ->
            BatEnum.for_all
              (fun (dimension, _) -> pred dimension)
              (Monomial.enum monomial))
    |> Rewrite.generators
    |> make

let project pred ideal =
  project_generators pred (generators ideal)

let intersect left right =
  let left_generators = generators left in
  let right_generators = generators right in
  let t =
    1 + List.fold_left
      (fun max_dimension polynomial ->
         try max max_dimension
               (SrkUtil.Int.Set.max_elt (QQXs.dimensions polynomial))
         with Not_found -> max_dimension)
      0
      (left_generators @ right_generators)
  in
  let left_generators =
    List.map (QQXs.mul (QQXs.of_dim t)) left_generators
  in
  let right_generators =
    List.map
      (QQXs.mul (QQXs.sub (QQXs.scalar QQ.one) (QQXs.of_dim t)))
      right_generators
  in
  project_generators ((<>) t) (left_generators @ right_generators)

let product left right =
  let left_generators = generators left in
  List.fold_left
    (fun product_generators left_polynomial ->
       List.fold_left
         (fun product_generators right_polynomial ->
            QQXs.mul left_polynomial right_polynomial :: product_generators)
         product_generators
         left_generators)
    []
    (generators right)
  |> make

let sum left right =
  let right_generators = generators right in
  if use_msolve_for (generators left @ right_generators) then
    make (generators left @ generators right)
  else List.fold_left add_saturate left right_generators

let mk_rewrite ideal = ideal

open Syntax
open BatPervasives

module QQXs = Polynomial.QQXs
module PC = PolynomialCone
module I = Polynomial.Rewrite
module Monomial = Polynomial.Monomial
module Solver = Abstract.Solver
module Plt = PolyhedronLatticeTiling

type t = PolynomialCone.t

let of_model_lira solver man terms =
  let srk = Abstract.Solver.get_context solver in
  let phi = Abstract.Solver.get_formula solver in
  function
  | `LIRR _ -> assert false
  | `LIRA model ->
    let polyhedron =
      fst (Plt.ConvexHull.cch_lira ~man srk terms (phi, model))
    in
    let (zero, pos) =
      BatEnum.fold (fun (zero, pos) (kind, vec) ->
          match kind with
          | `Zero -> ((QQXs.of_vec vec)::zero, pos)
          | `Nonneg | `Pos -> (zero, (QQXs.of_vec vec)::pos))
        ([], [])
        (DD.enum_constraints polyhedron)
    in
    PC.make_cone (I.mk_rewrite Monomial.degrevlex zero) pos

let of_model_lirr solver terms =
  let srk = Solver.get_context solver in
  let poly_terms = Array.map (QQXs.of_term srk) terms in
  function
  | `LIRA _ -> assert false
  | `LIRR m ->
    let cone = Lirr.Model.nonnegative_cone m in
    PolynomialCone.inverse_image cone poly_terms

let abstract solver ?(bottom=PC.make_cone (I.mk_rewrite Monomial.degrevlex [QQXs.one]) []) terms =
  let srk = Solver.get_context solver in
  let zero = mk_zero srk in
  let is_zero = mk_eq srk zero % QQXs.term_of srk (Array.get terms) in
  let is_nonneg = mk_leq srk zero % QQXs.term_of srk (Array.get terms) in
  let man = Polka.manager_alloc_loose () in
  let formula_of prop =
    mk_and srk ((List.map is_zero (I.generators (PC.get_ideal prop)))
                @ (List.map is_nonneg (PC.get_cone_generators prop)))
  in
  let join = PC.intersection in
  let top = PC.top in
  let of_model = match Solver.get_theory solver with
    | `LIRA -> of_model_lira solver man terms
    | `LIRR -> of_model_lirr solver terms
  in
  let domain =
    Abstract.{ join; top; of_model; bottom; formula_of }
  in
  Solver.abstract solver domain

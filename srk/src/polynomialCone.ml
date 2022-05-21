open Polynomial
open BatPervasives

include Log.Make(struct let name = "srk.polynomialCone" end)

type t = Rewrite.t * QQXs.t BatList.t
module V = Linear.QQVector
module PVCTX = PolynomialUtil.PolyVectorContext
module PV = PolynomialUtil.PolyVectorConversion

let pp pp_dim formatter pc =
  let ideal, cone = pc in
  Format.pp_print_string formatter "Ideal: ";
  Rewrite.pp pp_dim formatter ideal;
  Format.pp_print_string formatter " ";
  Format.pp_print_string formatter "Cone: ";
  SrkUtil.pp_print_list (QQXs.pp pp_dim) formatter cone

let get_ideal (ideal, _) = ideal

let make_cone ideal cone_gens = (ideal, cone_gens)

let get_cone_generators (_, cone_generators) = cone_generators

(* Change monomial ordering of a polynomial cone. *)
let change_monomial_ordering (ideal, cone) order =
  let new_ideal = Rewrite.reorder_groebner order ideal in
  (new_ideal,
   BatList.map (Rewrite.reduce new_ideal) cone)

module MonomialMap = BatMap.Make(Monomial)

let polyhedron_of_cone cone_generators ctx =
  let vec_generators = BatList.map
      (fun p -> PV.poly_to_vector ctx p)
      cone_generators
  in
  let constraints = BatEnum.map
      (fun v -> (`Nonneg, v))
      (BatList.enum vec_generators)
  in
  Polyhedron.of_constraints constraints

let extract_polynomial_constraints ctx polyhedron =
  let equality_constraints = Polyhedron.enum_constraints polyhedron |>
                             BatEnum.filter (fun (constraint_kind, _) ->
                                 match constraint_kind with
                                   `Zero -> true
                                 | _ -> false
                               )
                             (* use |> tap (fun intermediate -> print) *)
                             |> BatList.of_enum
                             |> BatList.map (fun (_, v) ->
                                 PV.vector_to_poly ctx v)
                             |> BatList.filter (fun p -> not (QQXs.equal p QQXs.zero))
  in
  let geq_zero_constraints = Polyhedron.enum_constraints polyhedron |>
                             BatEnum.filter (fun (constraint_kind, _) ->
                                 match constraint_kind with
                                   `Zero -> false
                                 | _ -> true
                               )
                             |> BatEnum.map (fun (_, v) -> PV.vector_to_poly ctx v)
                             |> BatList.of_enum
  in
  (equality_constraints, QQXs.one :: geq_zero_constraints)

(* Find implied zero polynomials via double description method *)
let _dd_find_implied_zero_polynomials polys =
  let polys = QQXs.one :: polys in
  let ctx = PVCTX.mk_context Monomial.degrevlex polys in
  let polyhedron = polyhedron_of_cone polys ctx |> Polyhedron.normalize_constraints in
  extract_polynomial_constraints ctx polyhedron

let find_implied_zero_polynomials polys =
  let polys = QQXs.one :: polys in
  let ctx = PVCTX.mk_context Monomial.degrevlex polys in
  let dim = PVCTX.num_dimensions ctx in
  let linear_cone =
    Cone.make ~lines:[] ~rays:(BatList.map (PV.poly_to_vector ctx) polys) dim
  in
  Cone.normalize linear_cone;
  (List.map (PV.vector_to_poly ctx) (Cone.lines linear_cone),
   List.map (PV.vector_to_poly ctx) (Cone.rays linear_cone))

let make_enclosing_cone basis geq_zero_polys =
  (* Assuming that in the arguments geq_zero_polys are reduced w.r.t. basis. *)
  let rec go basis geq_zero_polys =
    let new_zero_polys, new_geq_zero_polys = find_implied_zero_polynomials geq_zero_polys in
    if (BatList.length new_zero_polys) = 0 then
      (basis, geq_zero_polys)
    else
      let new_basis = BatList.fold_left
          (fun ideal zero_poly -> Rewrite.add_saturate ideal zero_poly)
          basis
          new_zero_polys
      in
      let reduced_geq_polys = BatList.map (Rewrite.reduce new_basis) new_geq_zero_polys in
      go new_basis reduced_geq_polys
  in
  let r = BatList.map (Rewrite.reduce basis) (QQXs.one :: geq_zero_polys) in
  go basis r

let add_polys_to_cone pc zero_polys nonneg_polys =
  let basis, cone_generators = pc in
  let new_basis = BatList.fold_left
      (fun ideal zero_poly -> Rewrite.add_saturate ideal zero_poly)
      basis
      zero_polys
  in
  make_enclosing_cone new_basis (BatList.concat [cone_generators; nonneg_polys])

let trivial = (Rewrite.mk_rewrite Monomial.degrevlex [QQXs.one], [])

let cone_of_polyhedron poly ctx =
  let zero_polys, geq_zero_polys = extract_polynomial_constraints ctx poly in
  let zero_polys = BatList.concat_map (fun p -> [QQXs.negate p; p]) zero_polys in
  let cone_generators = zero_polys @ geq_zero_polys in
  BatList.filter (fun p -> not (QQXs.equal p (QQXs.zero))) cone_generators

let project_cone cone_generators f =
  let cone_generators = QQXs.one :: cone_generators in
  let ctx = PVCTX.mk_context Monomial.degrevlex cone_generators in
  let dim = PVCTX.num_dimensions ctx in
  let polyhedron_rep_of_cone = polyhedron_of_cone cone_generators ctx in
  let elim_dims = (1 -- (dim - 1)) |> BatEnum.filter
                    (fun i ->
                       let monomial = PVCTX.monomial_of i ctx in
                       BatEnum.exists
                         (fun (d, _) -> f d)
                         (Monomial.enum monomial)
                    ) |> BatList.of_enum in
  let projected_polyhedron = Polyhedron.project elim_dims polyhedron_rep_of_cone in
  cone_of_polyhedron projected_polyhedron ctx

let monomial_over pred monomial =
  BatEnum.for_all (fun (d, _) -> pred d) (Monomial.enum monomial)

let polynomial_over pred polynomial =
  BatEnum.for_all (fun (_, m) -> monomial_over pred m) (QQXs.enum polynomial)

let project pc f =
  let elim_order = Monomial.block [not % f] Monomial.degrevlex in
  let (ideal, cone) = change_monomial_ordering pc elim_order in
  let dims_to_elim = not % f in
  let projected_ideal =
    Rewrite.generators ideal
    |> List.filter (polynomial_over f)
    |> Rewrite.mk_rewrite Monomial.degrevlex
  in
  let projected_cone = project_cone cone dims_to_elim in
  (projected_ideal, projected_cone)

let intersection (i1, c1) (i2, c2) =
  let i1_gen = Rewrite.generators i1 in
  let i2_gen = Rewrite.generators i2 in
  let fresh_var =
    1 + (List.fold_left
           (fun m p ->
              try max m (SrkUtil.Int.Set.max_elt (QQXs.dimensions p))
              with Not_found -> m)
           0
           (i1_gen @ i2_gen @ c1 @ c2))
  in
  let i1' = List.map (QQXs.mul (QQXs.of_dim fresh_var)) i1_gen in
  let c1' = List.map (QQXs.mul (QQXs.of_dim fresh_var)) c1 in
  let i2' = List.map (QQXs.mul (QQXs.sub (QQXs.scalar QQ.one) (QQXs.of_dim fresh_var))) i2_gen in
  let c2' = List.map (QQXs.mul (QQXs.sub (QQXs.scalar QQ.one) (QQXs.of_dim fresh_var))) c2 in
  let dims_to_elim = fun x -> x = fresh_var in
  let ideal =
    Rewrite.mk_rewrite (Monomial.block [dims_to_elim] Monomial.degrevlex) (i1' @ i2')
    |> Rewrite.grobner_basis
  in
  let ideal2 =
    Rewrite.generators ideal
    |> List.filter (polynomial_over (not % dims_to_elim))
    |> Rewrite.mk_rewrite Monomial.degrevlex
  in
  let reduced = (List.map (Rewrite.reduce ideal) (c1' @ c2')) in
  let cone = project_cone reduced (fun x -> x = fresh_var) in
  (ideal2, cone)


let equal (i1, c1) (i2, c2) =
  Rewrite.equal i1 i2
  && (let rewritten_c2 = List.map (Rewrite.reduce i1) c2 in
      try
        let pvutil = PVCTX.mk_context Monomial.degrevlex rewritten_c2 in
        (
          Polyhedron.equal
            (polyhedron_of_cone c1 pvutil)
            (polyhedron_of_cone rewritten_c2 pvutil))
      with PVCTX.Not_in_context -> false)

let to_formula srk term_of_dim (ideal, cone_generators) =
  let open Syntax in
  let ideal_eq_zero = BatList.map (fun p -> mk_eq srk (mk_real srk QQ.zero) (QQXs.term_of srk term_of_dim p))
      (Rewrite.generators ideal)
  in
  let gen_geq_zero = BatList.map (fun p -> mk_leq srk (mk_real srk QQ.zero) (QQXs.term_of srk term_of_dim p))
      cone_generators
  in
  mk_and srk (ideal_eq_zero @ gen_geq_zero)

let mem p (ideal, cone_generators) =
  let cone_generators = QQXs.one :: cone_generators in
  let reduced = Rewrite.reduce ideal p in
  let ctx = PVCTX.mk_context Monomial.degrevlex cone_generators in
  let p_monos = QQXs.enum reduced in
  (* Optimization: if a monomial appears in reduced but not cone_generators then return false
     immediately *)
  let m = PVCTX.get_mono_map ctx in
  if BatEnum.exists (fun (_, p_mono) ->
      not (MonomialMap.mem p_mono m))
      p_monos
  then
    false
  else
     begin
      let vec_target_poly = PV.poly_to_vector ctx reduced in
      let cone = polyhedron_of_cone cone_generators ctx in
      Polyhedron.mem (fun i -> V.coeff i vec_target_poly) cone
    end

let is_proper pc =
  not (mem (QQXs.negate QQXs.one) pc)

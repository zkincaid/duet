open Polynomial
open BatPervasives

include Log.Make(struct let name = "srk.polynomialCone" end)

type t = Ideal.t * QQXs.t BatList.t
module V = Linear.QQVector

let get_ideal pc =
  let ideal, _ = pc in
  ideal

let get_cone_generators pc =
  let _, cone_generators = pc in
  cone_generators

let make ideal cone_generators =
  (ideal, BatList.map (fun g -> Ideal.reduce ideal g) cone_generators)

let add_polynomial_to_ideal pc p =
  let ideal, cone = pc in
  make (Ideal.add_saturate ideal p) cone

let add_polynomial_to_cone pc p =
  let ideal, cone = pc in
  (ideal, Ideal.reduce ideal p :: cone)

let change_monomial_ordering pc order =
  let ideal, cone = pc in
  let new_ideal = Ideal.change_monomial_ordering ideal order in
  (new_ideal,
   BatList.map (fun g -> Ideal.reduce new_ideal g) cone)

module MonomialMap = BatMap.Make(Monomial)

let monomial_map_of_polynomial p =
  let mono_map = MonomialMap.empty in
  BatEnum.fold (fun m (coeff, monomial) ->  MonomialMap.add monomial coeff m)
    mono_map
    (QQXs.enum p)

let monomial_map_of_cone c =
  BatList.fold (fun map poly ->
      let f _ a b =
        match a, b with
        | Some a, _ -> Some a
        | _, Some b -> Some b
        | None, None -> assert false
      in
      MonomialMap.merge f map (monomial_map_of_polynomial poly))
    MonomialMap.empty
    c

let vec_of_poly p mono_map =
  let v = V.zero in
  BatEnum.fold (fun v (coeff, monomial) ->
      if monomial = Monomial.one then
        V.add_term coeff Linear.const_dim v
      else
        let idx = MonomialMap.find monomial mono_map in
        V.add_term coeff idx v)
    v
    (QQXs.enum p)

let order_monomial_terms_in_map mono_map =
  let result = MonomialMap.empty in
  BatEnum.foldi
    (fun i (monomial, _) map -> MonomialMap.add monomial i map)
    result
    (MonomialMap.enum mono_map)

let poly_of_vec vec ordered_mono_list =
  BatEnum.fold (fun p (coeff, index) ->
      let q = QQXs.add_term coeff (BatList.nth ordered_mono_list index) p in
      QQXs.add_term (QQ.negate coeff) (BatList.nth ordered_mono_list index) q)
    (QQXs.zero)
    (Linear.QQVector.enum vec)

let find_implied_zero_polynomials polys basis =
  let ordered_mono_map = order_monomial_terms_in_map (monomial_map_of_cone polys) in
  let ordered_mono_list = BatList.of_enum (MonomialMap.enum ordered_mono_map) |> BatList.map (fun (m, _) -> m) in
  let polys_as_vectors = BatList.map
      (fun p -> vec_of_poly p ordered_mono_map)
      polys
  in
  let polyhedron = BatEnum.map
      (fun v -> (`Nonneg, v))
      (BatList.enum polys_as_vectors)
                   |> Polyhedron.of_constraints
                   |> Polyhedron.affine_hull
  in
  let equality_constraints = Polyhedron.enum_constraints polyhedron |>
                             BatEnum.filter (fun (constraint_kind, _) ->
                                 match constraint_kind with
                                   `Zero -> true
                                 | _ -> false
                               )
                             |> BatList.of_enum
                             |> BatList.map (fun (_, v) ->
                                 Ideal.reduce basis (poly_of_vec v ordered_mono_list))
                             |> BatList.filter (fun p -> not (QQXs.equal p QQXs.zero))
  in
  let geq_zero_constraints = Polyhedron.enum_constraints polyhedron |>
                             BatEnum.filter (fun (constraint_kind, _) ->
                                 match constraint_kind with
                                   `Zero -> false
                                 | _ -> true
                               )
                             |> BatEnum.map (fun (_, v) -> poly_of_vec v ordered_mono_list)
                             |> BatList.of_enum
  in
  if (BatList.length equality_constraints) > 0 then
    (true, equality_constraints, geq_zero_constraints)
  else
    (false, equality_constraints, geq_zero_constraints)

let make_enclosing_cone poly_list =

  let rec make_enclosing_cone_impl finished basis geq_zero_polys =
    if finished then (basis, geq_zero_polys)
    else
      let is_finished, new_zero_polys, geq_zero_polys = find_implied_zero_polynomials geq_zero_polys basis in
      let new_basis = BatList.fold
          (fun ideal zero_poly -> Ideal.add_saturate ideal zero_poly)
          basis
          new_zero_polys
      in
      let reduced_geq_polys = BatList.map (fun p -> Ideal.reduce new_basis p) geq_zero_polys in
      make_enclosing_cone_impl is_finished new_basis reduced_geq_polys
  in

  let basis = Ideal.make [] in
  make_enclosing_cone_impl false basis poly_list

let project_cone cone_generators f =
  let ordered_mono_map = order_monomial_terms_in_map (monomial_map_of_cone cone_generators) in
  let ordered_mono_list = BatList.of_enum (MonomialMap.enum ordered_mono_map) |> BatList.map (fun (m, _) -> m) in
  let vec_generators = BatList.map
      (fun p -> vec_of_poly p ordered_mono_map)
      cone_generators
  in
  let generators_enum = BatEnum.map
      (fun v -> (`Ray, v))
      (BatList.enum vec_generators)
  in
  BatEnum.push generators_enum (`Vertex, V.zero);
  let dim = MonomialMap.cardinal ordered_mono_map in
  (* const_dim should be handled properly by Polyhedron.ml *)
  let polyhedron_rep_of_cone = Polyhedron.of_generators dim generators_enum in
  let remaining_dims = (0 -- (dim - 1)) |> BatEnum.filter
                         (fun i ->
                            let monomial = BatList.nth ordered_mono_list i in
                            BatEnum.for_all
                              (fun (d, _) -> f d)
                              (Monomial.enum monomial)
                         ) |> BatList.of_enum in
  let projected_polyhedron = Polyhedron.project remaining_dims polyhedron_rep_of_cone in
  (* TODO: Are these correct? *)
  let projected_cone_generators = BatEnum.map (fun (typ, vec_generator) ->
      match typ with
      |  `Ray ->
        BatEnum.fold (fun p (coeff, index) ->
            QQXs.add_term coeff (BatList.nth ordered_mono_list index) p)
          (QQXs.zero)
          (Linear.QQVector.enum vec_generator)
      | `Line -> BatEnum.fold (fun p (coeff, index) ->
          let q = QQXs.add_term coeff (BatList.nth ordered_mono_list index) p in
          QQXs.add_term (QQ.negate coeff) (BatList.nth ordered_mono_list index) q)
          (QQXs.zero)
          (Linear.QQVector.enum vec_generator)
      | `Vertex -> QQXs.zero
    )
      (Polyhedron.enum_generators dim projected_polyhedron)
                                  |> BatList.of_enum
  in BatList.filter (fun p -> not (QQXs.equal p (QQXs.zero))) projected_cone_generators

let project pc f =
  let (ideal, cone) = pc in
  let projected_ideal = Ideal.project f ideal in
  let projected_cone = project_cone cone f in
  (projected_ideal, projected_cone)

let intersection pc1 pc2 =
  let (i1, c1) = pc1 in
  let (i2, c2) = pc2 in
  let i1_gen = Ideal.generators i1 in
  let i2_gen = Ideal.generators i2 in
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
  let ideal = Ideal.make (i1' @ i2') in
  make ideal (c1' @ c2')

let polyhedron_of_cone cone_generators ordered_monomial_map =
  let vec_generators = BatList.map
      (fun p -> vec_of_poly p ordered_monomial_map)
      cone_generators
  in
  let generators_enum = BatEnum.map
      (fun v -> (`Ray, v))
      (BatList.enum vec_generators)
  in
  BatEnum.push generators_enum (`Vertex, V.zero);
  let dim = MonomialMap.cardinal ordered_monomial_map in
  Polyhedron.of_generators dim generators_enum

let equal pc1 pc2 =
  let (i1, c1) = pc1 in
  let (i2, c2) = pc2 in
  if not (Ideal.equal i1 i2) then false
  else let monomial_ordering = Ideal.get_monomial_ordering i1 in
    let i2' = Ideal.change_monomial_ordering i2 monomial_ordering in
    let (_, rewritten_c2) = make i2' c2 in
    let ordered_mono_map = order_monomial_terms_in_map (monomial_map_of_cone rewritten_c2) in
    Polyhedron.equal
      (polyhedron_of_cone c1 ordered_mono_map)
      (polyhedron_of_cone rewritten_c2 ordered_mono_map)

let mem p pc =
  let ideal, cone_generators = pc in
  let reduced = Ideal.reduce ideal p in
  (* Optimization: if a monomial appears in reduced but not cone_generators then return false
     immediately *)
  let mono_map =
    BatList.fold (fun map poly ->
        let f _ a b =
          match a, b with
          | Some a, _ -> Some a
          | _, Some b -> Some b
          | None, None -> assert false
        in
        MonomialMap.merge f map (monomial_map_of_polynomial poly))
      (monomial_map_of_polynomial p)
      cone_generators
  in
  let ordered_mono_map = order_monomial_terms_in_map mono_map in
  let vec_target_poly = vec_of_poly reduced ordered_mono_map in
  let cone = polyhedron_of_cone cone_generators ordered_mono_map in
  Polyhedron.mem (fun i -> V.coeff i vec_target_poly) cone

let is_proper pc =
  mem (QQXs.negate QQXs.one) pc

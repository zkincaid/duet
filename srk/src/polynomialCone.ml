open Polynomial
open BatPervasives

include Log.Make(struct let name = "srk.polynomialCone" end)

type t = Ideal.t * QQXs.t BatList.t
module V = Linear.QQVector

(* User should be able to give pp_dim *)
let pp_dim formatter i =
  let rec to_string i =
    if i = -1 then "1" else
    if i < 26 then
      Char.escaped (Char.chr (97 + i))
    else
      (to_string (i/26)) ^ (Char.escaped (Char.chr (97 + (i mod 26))))
  in
  Format.pp_print_string formatter (to_string i)

let pp formatter pc =
  let ideal, cone = pc in
  Format.pp_print_string formatter "Ideal: ";
  Ideal.pp pp_dim formatter ideal;
  Format.pp_print_string formatter "Cone: ";
  SrkUtil.pp_print_list (QQXs.pp pp_dim) formatter cone

let get_ideal (ideal, _) = ideal

let get_cone_generators (_, cone_generators) = cone_generators

let make ideal cone_generators =
  (ideal, BatList.map (fun g -> Ideal.reduce ideal g) cone_generators)

let empty = (Ideal.make [], [])

(* Change monomial ordering of a polynomial cone. *)
let change_monomial_ordering pc order =
  let ideal, cone = pc in
  let new_ideal = Ideal.change_monomial_ordering ideal order in
  (new_ideal,
   BatList.map (fun g -> Ideal.reduce new_ideal g) cone)

module MonomialMap = BatMap.Make(Monomial)

type pvutil = {
  mono_map: int MonomialMap.t;
  ordered_mono_list: Monomial.t list;
}

let monomial_map_of_polynomial p =
  let mono_map = MonomialMap.empty in
  BatEnum.fold (fun m (coeff, monomial) ->
      MonomialMap.add monomial coeff m)
    mono_map
    (QQXs.enum p)

let pvutil_of_polys polys =
  let map =
    BatList.fold (fun map poly ->
        let f _ a b =
          match a, b with
          | Some a, _ -> Some a
          | _, Some b -> Some b
          | None, None -> assert false
        in
        MonomialMap.merge f map (monomial_map_of_polynomial poly))
      MonomialMap.empty
      polys
  in
  let ordered_mono_map =
    BatEnum.foldi
      (fun i (monomial, _) map -> MonomialMap.add monomial i map)
      MonomialMap.empty
      (MonomialMap.enum map)
  in
  let ordered_mono_list =
    BatList.of_enum (MonomialMap.enum ordered_mono_map) |> BatList.map (fun (m, _) -> m) in
  {
    mono_map = ordered_mono_map;
    ordered_mono_list = ordered_mono_list;
  }

let pvutil_merge pvutil poly =
  let mono_map = BatEnum.fold (fun m (_, monomial) ->
      MonomialMap.add monomial 1 m)
      pvutil.mono_map
      (QQXs.enum poly)
  in
  let ordered_mono_map =
    BatEnum.foldi
      (fun i (monomial, _) map -> MonomialMap.add monomial i map)
      MonomialMap.empty
      (MonomialMap.enum mono_map)
  in
  let ordered_mono_list =
    BatList.of_enum (MonomialMap.enum ordered_mono_map) |> BatList.map (fun (m, _) -> m) in
  {
    mono_map = ordered_mono_map;
    ordered_mono_list = ordered_mono_list;
  }

let vec_of_poly p pvutil =
  let mono_map = pvutil.mono_map in
  let v = V.zero in
  BatEnum.fold (fun v (coeff, monomial) ->
      let idx = MonomialMap.find monomial mono_map in
      V.add_term coeff idx v)
    v
    (QQXs.enum p)

let poly_of_vec vec pvutil =
  let ordered_mono_list = pvutil.ordered_mono_list in
  BatEnum.fold (fun p (coeff, index) ->
      QQXs.add_term coeff (BatList.nth ordered_mono_list index) p)
    (QQXs.zero)
    (Linear.QQVector.enum vec)

let polyhedron_of_cone cone_generators pvutil =
  let vec_generators = BatList.map
      (fun p -> vec_of_poly p pvutil)
      cone_generators
  in
  let generators_enum = BatEnum.map
      (fun v -> (`Ray, v))
      (BatList.enum vec_generators)
  in
  BatEnum.push generators_enum (`Vertex, V.zero);
  let dim = MonomialMap.cardinal pvutil.mono_map in
  Polyhedron.of_generators dim generators_enum

let find_implied_zero_polynomials polys basis =
  let polys = QQXs.one :: polys in
  let pvutil = pvutil_of_polys polys in
  let polys_as_vectors = BatList.map
      (fun p -> vec_of_poly p pvutil)
      polys
  in
  BatList.iter (fun v -> logf "vector: %a" V.pp v) polys_as_vectors;
  logf "computing constraint representation of polyhedron";
  let polyhedron = BatEnum.map
      (fun v -> (`Nonneg, v))
      (BatList.enum polys_as_vectors)
                   |> Polyhedron.of_constraints
                   |> Polyhedron.normalize_constraints
  in
  logf "Polyhedron is: %a" (Polyhedron.pp pp_dim) polyhedron;
  let equality_constraints = Polyhedron.enum_constraints polyhedron |>
                             BatEnum.filter (fun (constraint_kind, _) ->
                                 match constraint_kind with
                                   `Zero -> true
                                 | _ -> false
                               )
                             (* use |> tap (fun intermediate -> print) *)
                             |> BatList.of_enum
                             |> BatList.map (fun (_, v) ->
                                 Ideal.reduce basis (poly_of_vec v pvutil))
                             |> BatList.filter (fun p -> not (QQXs.equal p QQXs.zero))
  in
  let geq_zero_constraints = Polyhedron.enum_constraints polyhedron |>
                             BatEnum.filter (fun (constraint_kind, _) ->
                                 match constraint_kind with
                                   `Zero -> false
                                 | _ -> true
                               )
                             |> BatEnum.map (fun (_, v) -> poly_of_vec v pvutil)
                             |> BatList.of_enum
  in
  (equality_constraints, geq_zero_constraints)

let rec make_enclosing_cone basis geq_zero_polys =
  let geq_zero_polys = QQXs.one :: geq_zero_polys in
  let new_zero_polys, geq_zero_polys = find_implied_zero_polynomials geq_zero_polys basis in
  if (BatList.length new_zero_polys) > 0 then
    let pc = (basis, geq_zero_polys) in
    logf "enclosing cone: %a" pp pc;
    pc
  else
    let new_basis = BatList.fold
        (fun ideal zero_poly -> Ideal.add_saturate ideal zero_poly)
        basis
        new_zero_polys
    in
    let reduced_geq_polys = BatList.map (fun p -> Ideal.reduce new_basis p) geq_zero_polys in
    make_enclosing_cone new_basis reduced_geq_polys

let add_polys_to_cone pc zero_polys nonneg_polys =
  let basis, cone_generators = pc in
  let new_basis = BatList.fold
      (fun ideal zero_poly -> Ideal.add_saturate ideal zero_poly)
      basis
      zero_polys
  in
  make_enclosing_cone new_basis (BatList.concat [cone_generators; nonneg_polys])

let cone_of_polyhedron poly pvutil =
  let dim = MonomialMap.cardinal pvutil.mono_map in
  let cone_generators = BatEnum.map (fun (typ, vec_generator) ->
      match typ with
      |  `Ray ->
        BatEnum.fold (fun p (coeff, index) ->
            QQXs.add_term coeff (BatList.nth pvutil.ordered_mono_list index) p)
          (QQXs.zero)
          (Linear.QQVector.enum vec_generator)
      (* salient cone should have no lines, thus the projection should also have no line *)
      | `Line -> failwith "Polyhedra of salient cones should have no line but encountered one"
      (* should always have one vertex at 0 *)
      | `Vertex -> QQXs.zero
    )
      (Polyhedron.enum_generators dim poly)
                        |> BatList.of_enum
  in BatList.filter (fun p -> not (QQXs.equal p (QQXs.zero))) cone_generators

let project_cone cone_generators f =
  let cone_generators = QQXs.one :: cone_generators in
  let pvutil = pvutil_of_polys cone_generators in
  let dim = MonomialMap.cardinal pvutil.mono_map in
  let polyhedron_rep_of_cone = polyhedron_of_cone cone_generators pvutil in
  let elim_dims = (0 -- (dim - 1)) |> BatEnum.filter
                    (fun i ->
                       let monomial = BatList.nth pvutil.ordered_mono_list i in
                       BatEnum.exists
                         (fun (d, _) -> not (f d))
                         (Monomial.enum monomial)
                    ) |> BatList.of_enum in
  let projected_polyhedron = Polyhedron.project elim_dims polyhedron_rep_of_cone in
  cone_of_polyhedron projected_polyhedron pvutil

let project pc f =
  let elim_order = Monomial.block [not % f] Monomial.degrevlex in
  let (ideal, cone) = change_monomial_ordering pc elim_order in
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
  let pc = make ideal (c1' @ c2') in
  project pc (fun d -> d != fresh_var)


let equal pc1 pc2 =
  let (i1, c1) = pc1 in
  let (i2, c2) = pc2 in
  if not (Ideal.equal i1 i2) then false
  else let monomial_ordering = Ideal.get_monomial_ordering i1 in
    let i2' = Ideal.change_monomial_ordering i2 monomial_ordering in
    let (_, rewritten_c2) = make i2' c2 in
    let pvutil = pvutil_of_polys rewritten_c2 in
    Polyhedron.equal
      (polyhedron_of_cone c1 pvutil)
      (polyhedron_of_cone rewritten_c2 pvutil)

let mem p pc =
  let ideal, cone_generators = pc in
  let cone_generators = QQXs.one :: cone_generators in
  let reduced = Ideal.reduce ideal p in
  let mmap_of_p = monomial_map_of_polynomial reduced in
  (* Optimization: if a monomial appears in reduced but not cone_generators then return false
     immediately *)
  let pvutil_of_cone = pvutil_of_polys cone_generators in
  if BatEnum.exists (fun (mono, _) ->
      not (MonomialMap.mem mono pvutil_of_cone.mono_map))
      (MonomialMap.enum mmap_of_p)
  then
    false
  else
    let pvutil = pvutil_merge pvutil_of_cone reduced in
    let vec_target_poly = vec_of_poly reduced pvutil in
    let cone = polyhedron_of_cone cone_generators pvutil in
    Polyhedron.mem (fun i -> V.coeff i vec_target_poly) cone

let is_proper pc =
  not (mem (QQXs.negate QQXs.one) pc)

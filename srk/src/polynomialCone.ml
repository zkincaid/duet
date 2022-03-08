open Polynomial
open BatPervasives

include Log.Make(struct let name = "srk.polynomialCone" end)

type t = Rewrite.t * QQXs.t BatList.t
module V = Linear.QQVector

let pp_dim formatter i =
  let rec to_string i =
    if i = -1 then "1" else
    if i < 26 then
      Char.escaped (Char.chr (97 + i))
    else
      (to_string (i/26)) ^ (Char.escaped (Char.chr (97 + (i mod 26))))
  in
  Format.pp_print_string formatter (to_string i)

(* test equality using the equal function not the pretty printing *)
let pp pp_dim formatter pc =
  try
    let ideal, cone = pc in
    Format.pp_print_string formatter "Ideal: ";
    Rewrite.pp pp_dim formatter ideal;
    Format.pp_print_string formatter " ";
    Format.pp_print_string formatter "Cone: ";
    SrkUtil.pp_print_list (QQXs.pp pp_dim) formatter cone
  with _ -> Format.printf "error in pp_dim cannot find associated symbol of dim"

let get_ideal (ideal, _) = ideal

(* let pp_dim srk = (fun formatter i -> Format.fprintf formatter "%a" (pp_symbol srk) (symbol_of_int i)) *)

let get_cone_generators (_, cone_generators) = cone_generators

(* Change monomial ordering of a polynomial cone. *)
let change_monomial_ordering (ideal, cone) order =
  let new_ideal = Rewrite.reorder_groebner order ideal in
  (new_ideal,
   BatList.map (Rewrite.reduce new_ideal) cone)

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
    BatList.fold_left (fun map poly ->
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
  logf "find_implied_zero_polynomials: computing constraint representation of polyhedron";
  let polyhedron = BatEnum.map
      (fun v -> (`Nonneg, v))
      (BatList.enum polys_as_vectors)
                   |> Polyhedron.of_constraints
                   |> Polyhedron.normalize_constraints
  in
  let equality_constraints = Polyhedron.enum_constraints polyhedron |>
                             BatEnum.filter (fun (constraint_kind, _) ->
                                 match constraint_kind with
                                   `Zero -> true
                                 | _ -> false
                               )
                             (* use |> tap (fun intermediate -> print) *)
                             |> BatList.of_enum
                             |> BatList.map (fun (_, v) ->
                                 Rewrite.reduce basis (poly_of_vec v pvutil))
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

let make_enclosing_cone basis geq_zero_polys =
  let rec go basis geq_zero_polys =
    let reduced = BatList.map (Rewrite.reduce basis) geq_zero_polys in
    let new_zero_polys, geq_zero_polys = find_implied_zero_polynomials reduced basis in

    if (BatList.length new_zero_polys) = 0 then
      begin
        logf "not getting any new zero polys, done";
        let reduced = BatList.map (Rewrite.reduce basis) geq_zero_polys in
        (* logf "enclosing cone: %a" pp pc; *)
        (basis, reduced)
      end
    else
      let new_basis = BatList.fold_left
          (fun ideal zero_poly -> Rewrite.add_saturate ideal zero_poly)
          basis
          new_zero_polys
      in
      let reduced_geq_polys = BatList.map (Rewrite.reduce new_basis) geq_zero_polys in
      go new_basis reduced_geq_polys
  in
  go basis (QQXs.one :: geq_zero_polys)

let add_polys_to_cone pc zero_polys nonneg_polys =
  let basis, cone_generators = pc in
  let new_basis = BatList.fold_left
      (fun ideal zero_poly -> Rewrite.add_saturate ideal zero_poly)
      basis
      zero_polys
  in
  make_enclosing_cone new_basis (BatList.concat [cone_generators; nonneg_polys])

let trivial = (Rewrite.mk_rewrite Monomial.degrevlex [QQXs.one], [])

let cone_of_polyhedron poly pvutil =
  Log.errorf "cone of polyhedron";
  let dim = MonomialMap.cardinal pvutil.mono_map in
  let cone_generators = BatEnum.map (fun (typ, vec_generator) ->
      match typ with
      |  `Ray ->
        Log.errorf "ray generator %a" V.pp vec_generator;
        BatEnum.fold (fun p (coeff, index) ->
            Log.errorf "before add term";
            QQXs.add_term coeff (BatList.nth pvutil.ordered_mono_list index) p)
          (QQXs.zero)
          (Linear.QQVector.enum vec_generator)
      (* salient cone should have no lines, thus the projection should also have no line *)
      | `Line -> Log.errorf "line generator %a" V.pp vec_generator;
        QQXs.one
      (* failwith "Polyhedra of salient cones should have no line but encountered one" *)
      (* should always have one vertex at 0 *)
      | `Vertex -> QQXs.zero
    )
      (Polyhedron.enum_generators dim poly)
                        |> BatList.of_enum
  in
  Log.errorf "after cone generators";
  BatList.filter (fun p -> not (QQXs.equal p (QQXs.zero))) cone_generators

let project_cone cone_generators f =
  Log.errorf "computing projection of cone part";
  let cone_generators = QQXs.one :: cone_generators in
  let pvutil = pvutil_of_polys cone_generators in
  let dim = MonomialMap.cardinal pvutil.mono_map in
  let polyhedron_rep_of_cone = polyhedron_of_cone cone_generators pvutil in
  Log.errorf "polyhedron of cone before proj";
  let elim_dims = (0 -- (dim - 1)) |> BatEnum.filter
                    (fun i ->
                       let monomial = BatList.nth pvutil.ordered_mono_list i in
                       BatEnum.exists
                         (fun (d, _) -> (f d))
                         (Monomial.enum monomial)
                    ) |> BatList.of_enum in
  Log.errorf "elim dims";
  let polys_of_elim_dims = BatList.enum (BatList.map (fun dim -> (`Zero, V.add_term QQ.one dim V.zero)) elim_dims) in

  Log.errorf "polys of elim dims";
  let p = Polyhedron.of_constraints polys_of_elim_dims in

  Log.errorf "polyhedron of constraints";
  let projected_polyhedron = Polyhedron.meet polyhedron_rep_of_cone p |> Polyhedron.normalize_constraints in
  cone_of_polyhedron projected_polyhedron pvutil

let monomial_over pred monomial =
  BatEnum.for_all (fun (d, _) -> pred d) (Monomial.enum monomial)

let polynomial_over pred polynomial =
  BatEnum.for_all (fun (_, m) -> monomial_over pred m) (QQXs.enum polynomial)

let project pc f =
  Log.errorf "computing projection of polynomial cone";
  let elim_order = Monomial.block [not % f] Monomial.degrevlex in
  let (ideal, cone) = change_monomial_ordering pc elim_order in
  Log.errorf "after changing mono ordering";
  let dims_to_elim = not % f in
  let projected_ideal =
    Rewrite.generators ideal
    |> List.filter (polynomial_over f)
    |> Rewrite.mk_rewrite Monomial.degrevlex
  in
  let projected_cone = project_cone cone dims_to_elim in
  (projected_ideal, projected_cone)

let intersection (i1, c1) (i2, c2) =
  Log.errorf "start intersecting";
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
  logf "fresh var has dim: %d" fresh_var;
  Log.errorf "fresh var is: %a" pp_dim fresh_var;
  let i1' = List.map (QQXs.mul (QQXs.of_dim fresh_var)) i1_gen in
  let c1' = List.map (QQXs.mul (QQXs.of_dim fresh_var)) c1 in
  let i2' = List.map (QQXs.mul (QQXs.sub (QQXs.scalar QQ.one) (QQXs.of_dim fresh_var))) i2_gen in
  let c2' = List.map (QQXs.mul (QQXs.sub (QQXs.scalar QQ.one) (QQXs.of_dim fresh_var))) c2 in
  let dims_to_elim = fun x -> x = fresh_var in
  let ideal =
    Rewrite.mk_rewrite (Monomial.block [dims_to_elim] Monomial.degrevlex) (i1' @ i2')
    |> Rewrite.grobner_basis
  in
  Log.errorf "ideal has generators";
  List.iter (fun p -> Log.errorf "=== %a ===" (QQXs.pp pp_dim) p) (Rewrite.generators ideal);
  let ideal2 =
    Rewrite.generators ideal
    |> List.filter (polynomial_over (not % dims_to_elim))
    |> Rewrite.mk_rewrite Monomial.degrevlex
  in
Log.errorf "ideal2 has generators";
  List.iter (fun p -> Log.errorf "=== %a ====" (QQXs.pp pp_dim) p) (Rewrite.generators ideal2);

  let reduced = (List.map (Rewrite.reduce ideal) (c1' @ c2')) in

Log.errorf "reduced cone has generators";
  List.iter (fun p -> Log.errorf "=== %a ===" (QQXs.pp pp_dim) p) (reduced);
  Log.errorf "before project";
  let cone = project_cone reduced (fun x -> x = fresh_var) in
Log.errorf "projected cone has generators";
  List.iter (fun p -> Log.errorf "=== %a ===" (QQXs.pp pp_dim) p) (cone);

  Log.errorf "returning";
  (ideal2, cone)

let equal (i1, c1) (i2, c2) =
  Rewrite.equal i1 i2
  && (let rewritten_c2 = List.map (Rewrite.reduce i1) c2 in
      try
        let pvutil = pvutil_of_polys rewritten_c2 in
        (
      Polyhedron.equal
        (polyhedron_of_cone c1 pvutil)
        (polyhedron_of_cone rewritten_c2 pvutil))
    with Not_found -> false)

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

open Polynomial
open BatPervasives

include Log.Make(struct let name = "srk.polynomialCone" end)

type t = Rewrite.t * QQXs.t BatList.t
module V = Linear.QQVector
module PVCTX = PolynomialUtil.PolyVectorContext
module PV = PolynomialUtil.PolyVectorConversion

let pp_dim formatter i =
  let rec to_string i =
    if i = -1 then "1" else
    if i < 26 then
      Char.escaped (Char.chr (97 + i))
    else
      (to_string (i/26)) ^ (Char.escaped (Char.chr (97 + (i mod 26))))
  in
  Format.pp_print_string formatter (to_string i)

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

let make_cone ideal cone_gens = (ideal, cone_gens)

let get_cone_generators (_, cone_generators) = cone_generators

(* Change monomial ordering of a polynomial cone. *)
let change_monomial_ordering (ideal, cone) order =
  let new_ideal = Rewrite.reorder_groebner order ideal in
  (new_ideal,
   BatList.map (Rewrite.reduce new_ideal) cone)

module MonomialMap = BatMap.Make(Monomial)

let polyhedron_of_cone cone_generators ctx =
  Log.errorf "computing polyhedron of cone";
  let vec_generators = BatList.map
      (fun p -> PV.poly_to_vector ctx p)
      cone_generators
  in
  let generators_enum = BatEnum.map
      (fun v -> Log.errorf "adding a ray of vector: %a" V.pp v;
        (`Ray, v))
      (BatList.enum vec_generators)
  in
  BatEnum.push generators_enum (`Vertex, V.zero);
  let dim = PVCTX.num_dimensions ctx in
  Polyhedron.of_generators dim generators_enum

let find_implied_zero_polynomials polys basis =
  let polys = QQXs.one :: polys in
  let ctx = PVCTX.mk_context ~fix_const_dim:false Monomial.degrevlex polys in
  let polys_as_vectors = BatList.map
      (fun p -> PV.poly_to_vector ctx p)
      polys
  in
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
                                 Rewrite.reduce basis (PV.vector_to_poly ctx v))
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
  (equality_constraints, geq_zero_constraints)

let make_enclosing_cone basis geq_zero_polys =
  (* Assuming that in the arguments geq_zero_polys are reduced w.r.t. basis. *)
  let rec go basis geq_zero_polys =
    let new_zero_polys, new_geq_zero_polys = find_implied_zero_polynomials geq_zero_polys basis in
    if (BatList.length new_zero_polys) = 0 then
      begin
        (* Log.errorf "not getting any new zero polys, done"; *)
        (basis, geq_zero_polys)
      end
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
  Log.errorf "cone of polyhedron";
  let dim = PVCTX.num_dimensions ctx in
  (* let dim = MonomialMap.cardinal pvutil.mono_map in *)
  let cone_generators = BatList.concat_map (fun (typ, vec_generator) ->
      match typ with
      |  `Ray ->
        logf "ray generator %a" V.pp vec_generator;
        let p =BatEnum.fold (fun p (coeff, index) ->
            QQXs.add_term coeff (PVCTX.monomial_of index ctx) p)
            (QQXs.zero)
            (Linear.QQVector.enum vec_generator)
        in [p]
      (* deal with lines as a pair of ray generation  *)
      | `Line -> logf "line generator %a" V.pp vec_generator;
        let p1 = BatEnum.fold (fun p (coeff, index) ->
            QQXs.add_term coeff (PVCTX.monomial_of index ctx) p)
            (QQXs.zero)
            (Linear.QQVector.enum vec_generator)
        in
        let p2 = BatEnum.fold (fun p (coeff, index) ->
            QQXs.add_term (QQ.negate coeff) (PVCTX.monomial_of index ctx) p)
            (QQXs.zero)
            (Linear.QQVector.enum vec_generator)
        in
        [p1; p2]
      (* should always have one vertex at 0 *)
      | `Vertex -> [QQXs.zero]
    )
      (BatList.of_enum (Polyhedron.enum_generators dim poly))
  in
  BatList.filter (fun p -> not (QQXs.equal p (QQXs.zero))) cone_generators

let project_cone cone_generators f =
  Log.errorf "computing projection of cone part";
  let cone_generators = QQXs.one :: cone_generators in
  let ctx = PVCTX.mk_context ~fix_const_dim:false Monomial.degrevlex cone_generators in
  let dim = PVCTX.num_dimensions ctx in
  Log.errorf "num dimension is: %d" dim;
  let polyhedron_rep_of_cone = polyhedron_of_cone cone_generators ctx in
  Log.errorf "polyhedron of cone before proj: %a" (Polyhedron.pp pp_dim) polyhedron_rep_of_cone;
  let elim_dims = (0 -- (dim - 1)) |> BatEnum.filter
                    (fun i ->
                       Log.errorf "finding monomial of dim: %d" i;
                       let monomial = PVCTX.monomial_of i ctx in
                       Log.errorf "found monomial: %a" (Monomial.pp pp_dim) monomial;
                       BatEnum.exists
                         (fun (d, _) ->
                            if (f d) then
                              Log.errorf "monomial that has dim %d var selected to be elim: %a" d (Monomial.pp pp_dim) monomial;
                            (f d))
                         (Monomial.enum monomial)
                    ) |> BatList.of_enum in
  Log.errorf "elim dims has dim %d" (BatList.length elim_dims);
  let polys_of_elim_dims = BatList.enum (BatList.map (fun dim -> (`Zero, V.add_term QQ.one dim V.zero)) elim_dims) in
  (* Log.errorf "polys of elim dims"; *)
  let p = Polyhedron.of_constraints polys_of_elim_dims in

  Log.errorf "elim polyhedron is: %a" (Polyhedron.pp pp_dim) p;
  (* Log.errorf "polyhedron of constraints"; *)
  let projected_polyhedron = Polyhedron.meet polyhedron_rep_of_cone p |> Polyhedron.normalize_constraints in
  Log.errorf "projected polyhedron is: %a" (Polyhedron.pp pp_dim) projected_polyhedron;
  cone_of_polyhedron projected_polyhedron ctx

let monomial_over pred monomial =
  BatEnum.for_all (fun (d, _) -> pred d) (Monomial.enum monomial)

let polynomial_over pred polynomial =
  BatEnum.for_all (fun (_, m) -> monomial_over pred m) (QQXs.enum polynomial)

let project pc f =
  Log.errorf "computing projection of polynomial cone";
  let elim_order = Monomial.block [not % f] Monomial.degrevlex in
  let (ideal, cone) = change_monomial_ordering pc elim_order in
  (* Log.errorf "after changing mono ordering"; *)
  let dims_to_elim = not % f in
  let projected_ideal =
    Rewrite.generators ideal
    |> List.filter (polynomial_over f)
    |> Rewrite.mk_rewrite Monomial.degrevlex
  in
  let projected_cone = project_cone cone dims_to_elim in
  (projected_ideal, projected_cone)

let intersection (i1, c1) (i2, c2) =
  Log.errorf "********* start intersecting";
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
  Log.errorf "fresh var has dim: %d" fresh_var;
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
  List.iter (fun p -> Log.errorf "=== (* %a *) ===" (QQXs.pp pp_dim) p) (reduced);
  let cone = project_cone reduced (fun x -> x = fresh_var) in
  Log.errorf "projected cone has generators";
  List.iter (fun p -> Log.errorf "=== %a ===" (QQXs.pp pp_dim) p) (cone);
  (* Log.errorf "returning"; *)
  (ideal2, cone)

(*
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
 *)

let equal (i1, c1) (i2, c2) =
  Rewrite.equal i1 i2
  && (
    let rewritten_c1 = List.map (Rewrite.reduce i2) c1 in
    let rewritten_c2 = List.map (Rewrite.reduce i1) c2 in
    let monos = List.map (fun p -> BatEnum.fold (fun l (_scalar, mono) -> mono :: l)
                             []
                             (QQXs.enum p))
        (rewritten_c1 @ rewritten_c2)
                |> List.concat in
    let context = PVCTX.context Monomial.degrevlex
        monos in
    let to_vectors polys =
      List.map (fun poly ->
          (`Nonneg, PV.poly_to_vector context poly))
        polys
      |> BatList.enum in
    let c1_vectors = to_vectors rewritten_c1 in
    let c2_vectors = to_vectors rewritten_c2 in
    Polyhedron.equal (Polyhedron.of_constraints c1_vectors) (Polyhedron.of_constraints c2_vectors))

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
  Log.errorf "checking membership for poly: %a" (QQXs.pp pp_dim) p;
  let cone_generators = QQXs.one :: cone_generators in
  let reduced = Rewrite.reduce ideal p in
  Log.errorf "reduced poly: %a" (QQXs.pp pp_dim) reduced;
  let ctx = PVCTX.mk_context ~fix_const_dim:false Monomial.degrevlex cone_generators in
  let p_monos = QQXs.enum reduced in
  (* Optimization: if a monomial appears in reduced but not cone_generators then return false
     immediately *)
  let m = PVCTX.get_mono_map ctx in
  if BatEnum.exists (fun (_, p_mono) ->
      not (MonomialMap.mem p_mono m))
      p_monos
  then
    begin
      Log.errorf "found monomial in p but not in ctx";
      false
    end
  else
    begin
      Log.errorf "did not find monomial in p but not in ctx";
      let pvutil = PVCTX.context_expand ctx reduced in
      let vec_target_poly = PV.poly_to_vector ctx reduced in
      Log.errorf "target vector is: %a " V.pp vec_target_poly;
      let cone = polyhedron_of_cone cone_generators pvutil in
      Log.errorf "cone polyhedron is: %a" (Polyhedron.pp pp_dim) cone;
      Polyhedron.mem (fun i -> V.coeff i vec_target_poly) cone
    end

let is_proper pc =
  not (mem (QQXs.negate QQXs.one) pc)

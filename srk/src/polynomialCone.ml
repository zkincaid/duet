open Polynomial
open BatPervasives

include Log.Make(struct let name = "srk.polynomialCone" end)

type t = Rewrite.t * QQXs.t BatList.t
module V = Linear.QQVector

module QQXs = Polynomial.QQXs
module PV = Polynomial.LinearQQXs

let pp pp_dim formatter (ideal, cone) =
  Format.fprintf
    formatter
    "Ideal: @[<v 0>%a@]@;Cone: @[<v 0>%a@]"
    (Rewrite.pp pp_dim) ideal
    (SrkUtil.pp_print_enum_nobox
       ~pp_sep:Format.pp_print_space (QQXs.pp pp_dim))
    (BatList.enum cone)

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
  BatList.enum cone_generators
  /@ (fun p -> (`Nonneg, PV.densify ctx p))
  |> Polyhedron.of_constraints

let extract_polynomial_constraints ctx polyhedron =
  let equality_constraints = Polyhedron.enum_constraints polyhedron |>
                             BatEnum.filter (fun (constraint_kind, _) ->
                                 match constraint_kind with
                                   `Zero -> true
                                 | _ -> false
                               )
                             (* use |> tap (fun intermediate -> print) *)
                             |> BatList.of_enum
                             |> BatList.map (fun (_, v) -> PV.sparsify ctx v)
                             |> BatList.filter (fun p -> not (QQXs.equal p QQXs.zero))
  in
  let geq_zero_constraints = Polyhedron.enum_constraints polyhedron |>
                             BatEnum.filter (fun (constraint_kind, _) ->
                                 match constraint_kind with
                                   `Zero -> false
                                 | _ -> true
                               )
                             |> BatEnum.map (fun (_, v) -> PV.sparsify ctx v)
                             |> BatList.of_enum
  in
  (equality_constraints, QQXs.one :: geq_zero_constraints)

let find_implied_zero_polynomials polys =
  let polys = QQXs.one :: polys in
  let ctx = PV.min_context (BatList.enum polys) in
  let dim = PV.dim ctx in
  let linear_cone =
    Cone.make ~lines:[] ~rays:(BatList.map (PV.densify ctx) polys) dim
  in
  Cone.normalize linear_cone;
  (List.map (PV.sparsify ctx) (Cone.lines linear_cone),
   List.map (PV.sparsify ctx) (Cone.rays linear_cone))

let regularize basis geq_zero_polys =
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

let add_generators ?zeros ?nonnegatives pc =

  let zero_polys = match zeros with None -> [] | Some p -> p in
  let nonneg_polys = match nonnegatives with None -> [] | Some p -> p in
  let basis, cone_generators = pc in
  let new_basis = BatList.fold_left
      (fun ideal zero_poly -> Rewrite.add_saturate ideal zero_poly)
      basis
      zero_polys
  in
  regularize new_basis (BatList.concat [cone_generators; nonneg_polys])

let top = (Rewrite.mk_rewrite Monomial.degrevlex [QQXs.one], [])

let cone_of_polyhedron poly ctx =
  let zero_polys, geq_zero_polys = extract_polynomial_constraints ctx poly in
  let zero_polys = BatList.concat_map (fun p -> [QQXs.negate p; p]) zero_polys in
  let cone_generators = zero_polys @ geq_zero_polys in
  BatList.filter (fun p -> not (QQXs.equal p (QQXs.zero))) cone_generators

let project_cone cone_generators f =
  let ctx = PV.min_context (BatList.enum cone_generators) in
  let dim = PV.dim ctx in
  let polyhedron_rep_of_cone = polyhedron_of_cone cone_generators ctx in
  let elim_dims =
    (0 -- (dim - 1))
    |> BatEnum.filter (fun i -> not (f (PV.dim_of_int ctx i)))
    |> BatList.of_enum
  in
  let projected_polyhedron =
    Polyhedron.project_dd elim_dims polyhedron_rep_of_cone
  in
  cone_of_polyhedron projected_polyhedron ctx

let restrict f (ideal, cone) = (Rewrite.restrict f ideal, project_cone cone f)

let monomial_over pred monomial =
  BatEnum.for_all (fun (d, _) -> pred d) (Monomial.enum monomial)

let polynomial_over pred polynomial =
  BatEnum.for_all (fun (_, m) -> monomial_over pred m) (QQXs.enum polynomial)

let project pc f =
  let elim_order = Monomial.block [not % f] Monomial.degrevlex in
  let (ideal, cone) = change_monomial_ordering pc elim_order in
  let elim m = BatEnum.for_all (f % fst) (Monomial.enum m) in
  let projected_ideal =
    Rewrite.generators ideal
    |> List.filter (polynomial_over f)
    |> Rewrite.mk_rewrite Monomial.degrevlex
  in
  let projected_cone = project_cone cone elim in
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
  let cone =
    project_cone
      reduced
      (BatEnum.for_all (fun (v, _) -> v != fresh_var) % Monomial.enum)
  in
  (ideal2, cone)

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
  let cone_generators = cone_generators in
  let reduced = Rewrite.reduce ideal p in
  let ctx = PV.min_context (BatList.enum cone_generators) in
  (* Optimization: if a monomial appears in reduced but not cone_generators
     then return false immediately *)
  if BatEnum.exists (fun (_, p_mono) ->
      not (PV.mem ctx p_mono))
      (QQXs.enum reduced)
  then
    false
  else
     begin
      let vec_target_poly = PV.densify ctx reduced in
      let dim = PV.dim ctx in
      let cone =
        let rays =
          BatList.map (PV.densify ctx) cone_generators
        in
        Cone.make ~lines:[] ~rays dim
      in
      Cone.mem vec_target_poly cone
    end

let leq (z1, p1) (z2, p2) =
  Rewrite.subset z1 z2
  && List.for_all (fun p -> mem p (z2, p2)) p1

let equal (z1, p1) (z2, p2) =
  Rewrite.equal z1 z2
  && List.for_all (fun p -> mem p (z2, p2)) p1
  && List.for_all (fun p -> mem p (z1, p1)) p2

let is_proper (ideal, _) =
  not (QQXs.equal QQXs.zero (Rewrite.reduce ideal QQXs.one))

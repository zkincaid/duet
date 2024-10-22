open Syntax

(* open BatPervasives *)
module Vec = Linear.QQVector
module TF = TransitionFormula
module CS = CoordinateSystem
module LIRR = Lirr
module P = Polynomial
module PC = PolynomialCone
module IS = Iteration.Solver

include Log.Make (struct
  let name = "TerminationPRF"
end)

let pp_dim srk arr formatter i =
  try
    Format.fprintf formatter "%a" (Syntax.ArithTerm.pp srk) (BatArray.get arr i)
  with _ -> Format.fprintf formatter "1"

let zero_stable solver pre_vars_arr post_vars_arr =
  let srk = Abstract.Solver.get_context solver in
  let conseq_pre = ConsequenceCone.abstract solver pre_vars_arr in
  logf "conseq pre: %a" (PC.pp (pp_dim srk pre_vars_arr)) conseq_pre;
  let rec work prev_cone =
    let pre_zeros = PC.get_ideal prev_cone in
    let zero_guards = P.Rewrite.generators pre_zeros in
    let zero_guards_remain_zero =
      BatList.map
        (fun pre_poly ->
          (* let pre_term = P.QQXs.term_of srk (Array.get pre_vars_arr) pre_poly in *)
          let post_term =
            P.QQXs.term_of srk (Array.get post_vars_arr) pre_poly
          in
          mk_eq srk (mk_zero srk) post_term)
        zero_guards
    in
    Abstract.Solver.add solver zero_guards_remain_zero;
    let new_cone = ConsequenceCone.abstract solver pre_vars_arr in
    if not (P.Rewrite.equal (PC.get_ideal prev_cone) (PC.get_ideal new_cone)) then
      work new_cone
  in
  work conseq_pre

let lin_conseq_over_diff_polys solver pre_vars_arr post_vars_arr positive_polys =
  let srk = Abstract.Solver.get_context solver in
  let diffs_arr =
    Array.map
      (fun poly ->
        let pre_poly_term =
          P.QQXs.term_of srk (fun dim -> BatArray.get pre_vars_arr dim) poly
        in
        let post_poly_term =
          P.QQXs.term_of srk (fun dim -> BatArray.get post_vars_arr dim) poly
        in
        mk_sub srk pre_poly_term post_poly_term)
      positive_polys
  in
  let lin_conseq = ConvexHull.abstract solver diffs_arr in
  logf "lin conseq over positives: %a" (DD.pp (pp_dim srk diffs_arr)) lin_conseq;
  (lin_conseq, diffs_arr)

let has_prf solver =
  let srk = Iteration.Solver.get_context solver in
  let abs_solver = Iteration.Solver.get_abstract_solver solver in
  let x_xp =
    Symbol.Set.fold
      (fun s xs -> (s, s) :: xs)
      (IS.get_constants solver)
      (IS.get_symbols solver)
  in
  logf "Finding PRF for TF: %a" (Formula.pp srk) (IS.get_formula solver);
  let pre_vars_arr =
    BatArray.of_list (BatList.map (fun (x, _) -> mk_const srk x) x_xp)
  in
  let post_vars_arr =
    BatArray.of_list (BatList.map (fun (_, xp) -> mk_const srk xp) x_xp)
  in
  Abstract.Solver.push abs_solver;
  zero_stable abs_solver pre_vars_arr post_vars_arr;
  logf "zero-stable formula: %a" (Formula.pp srk) (IS.get_formula solver);
  let pre_conseq_cone = ConsequenceCone.abstract abs_solver pre_vars_arr in
  logf "conseq pre: %a" (PC.pp (pp_dim srk pre_vars_arr)) pre_conseq_cone;
  let pos_pre_polys = PC.get_cone_generators pre_conseq_cone in
  let dim = List.length pos_pre_polys in
  let phedral_new_terms, diffs_arr =
    lin_conseq_over_diff_polys
      abs_solver
      pre_vars_arr
      post_vars_arr
      (Array.of_list pos_pre_polys)
  in
  let constraints_enum = DD.enum_constraints_closed phedral_new_terms in
  let new_generators =
    BatEnum.fold
      (fun gens cons ->
        match cons with
        | `Nonneg, v ->
            (* logf "nonneg constraint as generator: %a" Vec.pp v; *)
            let b, vv = Vec.pivot Linear.const_dim v in
            let vv = Vec.add_term b dim vv in
            logf "nonneg constraint as generator: %a" Vec.pp vv;

            (`Ray, vv) :: gens
        | `Zero, v ->
            let b, vv = Vec.pivot Linear.const_dim v in
            let vp = Vec.add_term b dim vv in
            let vm = Vec.negate vp in
            logf "zero constraint as generator: %a" Vec.pp vp;
            logf "zero constraint as generator: %a" Vec.pp vm;

            (`Ray, vp) :: (`Ray, vm) :: gens)
      [ (`Vertex, Vec.zero) ]
      constraints_enum
  in
  let gen_enum = BatList.enum new_generators in
  let new_polyhedron = DD.of_generators (dim + 1) gen_enum in
  logf "polyhedron of nonneg diff terms constructed";
  let const_dim_minus_1_cons =
    Vec.add_term QQ.one Linear.const_dim (Vec.add_term QQ.one dim Vec.zero)
  in
  let const_dim_cons = (`Zero, const_dim_minus_1_cons) in
  let other_dims_positive =
    let open BatEnum in
    0 -- (dim - 1)
    |> BatList.of_enum
    |> BatList.map (fun d ->
           let v = Vec.add_term QQ.one d Vec.zero in
           (`Nonneg, v))
  in
  logf "polyhedron of -1 const terms constructed";

  let result =
    DD.meet_constraints new_polyhedron (const_dim_cons :: other_dims_positive)
  in

  let diffs_arr = Array.append diffs_arr (Array.make 1 (mk_one srk)) in
  logf "after intersection: %a" (DD.pp (pp_dim srk diffs_arr)) result;
  let ans = not (BatEnum.is_empty (DD.enum_generators result)) in
  logf "has prf: %b" ans;
  Abstract.Solver.pop abs_solver;
  ans

let has_plrf solver =
  let srk = Iteration.Solver.get_context solver in
  let abs_solver = Iteration.Solver.get_abstract_solver solver in
  let x_xp =
    Symbol.Set.fold
      (fun s xs -> (s, s) :: xs)
      (IS.get_constants solver)
      (IS.get_symbols solver)
  in
  logf "Begin PLRF for TF: %a" (Formula.pp srk) (Abstract.Solver.get_formula abs_solver);
  let pre_vars_arr =
    BatArray.of_list (BatList.map (fun (x, _) -> mk_const srk x) x_xp)
  in
  let post_vars_arr =
    BatArray.of_list (BatList.map (fun (_, xp) -> mk_const srk xp) x_xp)
  in

  let find_qrfs () =
    logf "current TF: %a" (Formula.pp srk) (Abstract.Solver.get_formula abs_solver);
    let pre_conseq_cone =
      ConsequenceCone.abstract abs_solver pre_vars_arr
    in
    logf "conseq pre: %a" (PC.pp (pp_dim srk pre_vars_arr)) pre_conseq_cone;
    let pos_pre_polys = PC.get_cone_generators pre_conseq_cone in
    let dim = List.length pos_pre_polys in
    let phedral_new_terms, diffs_arr =
      lin_conseq_over_diff_polys
        abs_solver
        pre_vars_arr
        post_vars_arr
        (Array.of_list pos_pre_polys)
    in
    let phedron =
      Polyhedron.of_constraints (DD.enum_constraints phedral_new_terms)
    in
    logf "phedron: %a" (Polyhedron.pp (pp_dim srk diffs_arr)) phedron;
    let dc = Polyhedron.dd_of dim (Polyhedron.dual_cone dim phedron) in
    let all_dims_positive =
      let open BatEnum in
      0 -- (dim - 1)
      |> BatList.of_enum
      |> BatList.map (fun d ->
             let v = Vec.add_term QQ.one d Vec.zero in
             (`Nonneg, v))
    in
    let dc = DD.meet_constraints dc all_dims_positive in
    logf "poly before qrfs: %a" (DD.pp (pp_dim srk diffs_arr)) dc;

    let qrfs =
      DD.enum_generators dc
      |> BatEnum.filter_map (fun (typ, vec) ->
             if typ = `Ray then
               let pre_exp =
                 Linear.term_of_vec srk
                   (fun d ->
                     let poly = BatList.nth pos_pre_polys d in
                     P.QQXs.term_of srk (Array.get pre_vars_arr) poly)
                   vec
               in
               let post_exp =
                 Linear.term_of_vec srk
                   (fun d ->
                     let poly = BatList.nth pos_pre_polys d in
                     P.QQXs.term_of srk (Array.get post_vars_arr) poly)
                   vec
               in
               Some (mk_eq srk pre_exp post_exp)
             else None)
      |> BatList.of_enum
    in
    qrfs
  in

  let rec termination_by_qrfs () =
    zero_stable abs_solver pre_vars_arr post_vars_arr;
    logf "zero-stable formula: %a" (Formula.pp srk) (Abstract.Solver.get_formula abs_solver);
    match Abstract.Solver.check abs_solver with
    | `Unsat ->
        logf "has PLRF!!";
        true
    | `Unknown ->
        logf "Unknown!";
      false
    | _ ->
      let qrfs = find_qrfs () in
      let improvement = mk_and srk qrfs in
      List.iter (logf "qrf unchange: %a" (Formula.pp srk)) qrfs;
      Abstract.Solver.push abs_solver;
      Abstract.Solver.add abs_solver [mk_not srk improvement];
      let check = Abstract.Solver.check abs_solver in
      Abstract.Solver.pop abs_solver;
      logf "improvement formula: %a" (Formula.pp srk) improvement;
      match check with
      | `Unsat | `Unknown ->
        logf "does not have PLRF :( ";
        false
      | `Sat ->
        Abstract.Solver.add abs_solver qrfs;
        termination_by_qrfs ()
  in
  Abstract.Solver.push abs_solver;
  let result = termination_by_qrfs () in
  Abstract.Solver.pop abs_solver;
  result

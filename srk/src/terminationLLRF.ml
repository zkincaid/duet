open Syntax
module Vec = Linear.QQVector
module Mat = Linear.QQMatrix
module TF = TransitionFormula

include Log.Make(struct let name = "TerminationLLRF" end)

type analysis_result = ProvedToTerminate | Unknown

(** This is a utility function that creates the delta symbols for each variable symbol,
    and relates the delta symbols with the original variable symbols by specifying
    that each dx = x' - x.
*)
let add_diff_terms_to_formula srk f x_xp =
  List.fold_right
    (fun (x, xp) (f, dx_list, dx_sym_set) -> 
       let dname = String.concat "" ["d_"; show_symbol srk x] in
       let cx = mk_const srk x in
       let cxp = mk_const srk xp in 
       let diff = mk_sub srk cxp cx in
       let dx_sym = mk_symbol srk ~name:dname `TyInt in
       let dx = mk_const srk dx_sym in
       let f_with_dx = mk_and srk [f ; mk_eq srk dx diff] in
       (f_with_dx, 
        List.cons dx_sym dx_list,
        Symbol.Set.add dx_sym dx_sym_set)
    )
    x_xp
    (f, [], Symbol.Set.empty)


(** Resursively computing quasi-linear ranking function for termination. 
    formula: current formula to reason about
    x_space_cs: coordinate system that maps integers to transition variable x's
    dx_space_cs: coordinate system that maps integers to corresponding delta variables,
        order agrees with x_space_cs
    dual_space_cs: coordinate system that maps integers i to the coefficient of the i-th transition variable 
      in the linear functional
    x_xp: pairs of x and x' variables
    dx_set: set of delta variables 
    x_set: set of transition variables
*)
let rec compute_quasi_ranking_functions srk formula x_space_cs dx_space_cs dual_space_cs dual_space_dim x_xp dx_set x_set =

  let compute_non_inc_cone formula = 
    let polka = Polka.manager_alloc_strict () in
    let f = rewrite srk ~down:(nnf_rewriter srk) formula in
    let property_of_dx =
      let exists x = Symbol.Set.mem x dx_set in
      Abstract.abstract ~exists:exists srk polka f
    in
    let formula_of_dx = SrkApron.formula_of_property property_of_dx in
    let dx_ineqs = Polyhedron.of_formula dx_space_cs formula_of_dx in
    let dual = Polyhedron.dual_cone dx_ineqs in 
    let constraints = Polyhedron.enum_constraints dual in
    let neg_constraints = BatEnum.map (fun (typ, v) -> (typ, Linear.QQVector.negate v)) constraints in
    let neg_dual = Polyhedron.of_constraints neg_constraints in
    neg_dual
  in 

  let compute_lower_bounded_cone formula = 
    let polka = Polka.manager_alloc_strict () in
    let f = rewrite srk ~down:(nnf_rewriter srk) formula in
    let property_of_x =
      let exists x = Symbol.Set.mem x x_set in
      Abstract.abstract ~exists:exists srk polka f
    in
    let formula_of_lbx = SrkApron.formula_of_property property_of_x in
    let poly = Polyhedron.of_formula x_space_cs formula_of_lbx in
    let constraints = Polyhedron.enum_constraints poly in
    let lb_cone_generators = BatEnum.map (
      fun (constraint_kind, v) -> 
        match constraint_kind with 
        | `Nonneg | `Pos -> let _, w = Linear.QQVector.pivot (-1) v in (`Ray, w)
        | `Zero -> let _, w = Linear.QQVector.pivot (-1) v in (`Line, w)
      ) 
      constraints 
    in
    (* Origin must belong to the lower-bounded terms cone *)
    BatEnum.push lb_cone_generators (`Vertex, Linear.QQVector.zero);
    let generators_list = BatList.of_enum lb_cone_generators in
    let lb_cone = Polyhedron.of_generators dual_space_dim (BatList.enum generators_list) in
    lb_cone
  in

  logf "calculating meet of non-inc cone and lower-bounded cone";
  let non_inc_cone = compute_non_inc_cone formula in
  if Polyhedron.equal non_inc_cone Polyhedron.bottom then
  begin
    logf ~attributes:[`Bold; `Red] "Non-increasing term cone is empty, LLRF fail";
    (false, formula) 
  end
  else 
  begin
    let lb_cone = compute_lower_bounded_cone formula in
    if Polyhedron.equal non_inc_cone Polyhedron.bottom then
      begin
        logf ~attributes:[`Bold; `Red] "Lower-bounded term cone is empty, LLRF fail";
        (false, formula) 
      end
    else 
      begin
        let quasi_rf_cone = Polyhedron.meet non_inc_cone lb_cone in
        logf "qrf cone: %a" (Formula.pp srk) (Polyhedron.to_formula dual_space_cs quasi_rf_cone);
        if Polyhedron.equal quasi_rf_cone Polyhedron.bottom then
          begin
            logf ~attributes:[`Bold; `Red] "Quasi-ranking function cone is empty, LLRF fail";
            (false, formula) 
          end
        else 
          begin 
            let qrf_cone_generators = BatList.of_enum (Polyhedron.enum_generators dual_space_dim quasi_rf_cone) in
            let coeff_all_zero = not (BatList.exists (fun (typ, _) -> match typ with | `Ray | `Line -> true | _ -> false) qrf_cone_generators) in
            if coeff_all_zero then 
              begin
                logf ~attributes:[`Bold; `Red] "only all zero quasi ranking function exists at this level, fail";
                (false, formula) 
              end
            else
              begin
                let qrf_unchange_constraints = BatList.map 
                  (fun (gen_kind, vec) -> 
                    match gen_kind with 
                    | `Vertex -> mk_true srk
                    | `Ray ->
                      logf "looking at generator with vector: %a" Linear.QQVector.pp vec;
                      let unprimed_exp = Linear.term_of_vec srk (fun d -> let x, _ = BatList.nth x_xp d in mk_const srk x) vec in
                      let primed_exp = Linear.term_of_vec srk (fun d -> let _, xp = BatList.nth x_xp d in mk_const srk xp) vec in
                      mk_eq srk unprimed_exp primed_exp
                    | `Line -> 
                      let zero_term = Linear.term_of_vec srk (fun d -> let x, _ = BatList.nth x_xp d in mk_const srk x) vec in
                      mk_eq srk (mk_zero srk) zero_term
                  ) 
                  qrf_cone_generators 
                in
                let constrained_formula = mk_and srk (formula :: qrf_unchange_constraints) in
                logf "Constrained formula for the next level is: %a" (Formula.pp srk) constrained_formula;
                match Smt.equiv srk formula constrained_formula with
                | `Unknown -> 
                    logf ~attributes:[`Bold; `Red] "Cannot decide if there is any improvement at this level"; (false, formula)
                | `Yes -> 
                    logf ~attributes:[`Bold; `Red] "No improvement at this level, halt LLRF synthesis"; (false, formula)
                | `No -> 
                    logf ~attributes:[`Bold; `Green] "There is improvement at this level";
                    match Smt.get_model srk constrained_formula with
                    | `Sat _ -> 
                      logf ~attributes:[`Bold; `Yellow] "Transition formula SAT, try to synthesize next depth";
                      compute_quasi_ranking_functions srk constrained_formula x_space_cs dx_space_cs dual_space_cs dual_space_dim x_xp dx_set x_set 
                    | `Unknown -> failwith "SMT solver should not return unknown"
                    | `Unsat -> (logf ~attributes:[`Bold; `Green] "Transition formula UNSAT, done"); (true, formula)
              end
          end
      end
  end

(** Mortal precondition operator via lexicographic linear ranking function (LLRF) synthesis.
    Returns a tuple (result, residual_formula) where the residual formula is a subset of 
    the original transition whose termination cannot be proved by synthesizing LLRFs.
 *)
let mp_llrf srk tf =
  let tf = TF.linearize srk tf in
  let all_symbols = Symbol.Set.to_list (symbols (TF.formula tf)) in
  let constant_symbols = List.filter (TF.is_symbolic_constant tf) all_symbols in
  let x_xp =
    List.fold_left (fun l s -> (s, s) :: l) (TF.symbols tf) constant_symbols
  in
  match Smt.get_model srk (TF.formula tf) with
  | `Sat _ -> 
    let x_list = List.fold_right (fun (sp, _) l -> sp :: l ) x_xp [] in
    let x_set = TF.pre_symbols x_xp in
    let f_with_dx, dx_list, dx_set =
      add_diff_terms_to_formula srk (TF.formula tf) x_xp
    in
    logf "formula with delta variables: %a" (Formula.pp srk) f_with_dx;
    let dual_space_cs = CoordinateSystem.mk_empty srk in
      List.iter (
        fun (x, _)-> 
          let term_name = "coeff_" ^ (show_symbol srk x) in
            CoordinateSystem.admit_term dual_space_cs (mk_const srk (mk_symbol srk (typ_symbol srk x) ~name:term_name))
      ) x_xp;
    let dual_space_dim = CoordinateSystem.dim dual_space_cs in
    let x_space_cs, dx_space_cs = CoordinateSystem.mk_empty srk, CoordinateSystem.mk_empty srk in
      List.iter2 (
        fun x dx -> 
            CoordinateSystem.admit_term x_space_cs (mk_const srk x);
            CoordinateSystem.admit_term dx_space_cs (mk_const srk dx);
            ()
      ) x_list dx_list;
    let (success, residual_formula) =
      compute_quasi_ranking_functions srk f_with_dx x_space_cs dx_space_cs dual_space_cs dual_space_dim x_xp dx_set x_set
    in 
      if success then (ProvedToTerminate, mk_false srk) else (Unknown, residual_formula) 
  | `Unknown -> logf "SMT solver should not return unknown for QRA formulas"; (Unknown, mk_true srk)
  | `Unsat -> (logf ~attributes:[`Bold; `Yellow] "Transition formula UNSAT, nothing to do"); (ProvedToTerminate, mk_false srk)

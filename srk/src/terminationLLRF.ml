open Syntax
module Vec = Linear.QQVector
module Mat = Linear.QQMatrix
module TF = TransitionFormula

include Log.Make(struct let name = "TerminationLLRF" end)

type analysis_result = ProvedToTerminate | Unknown

(** Transform a formula representation of a convex set f into a list of linear 
    inequalities. The linear inequalities are vectors where the meaning
    of the dimensions are given by the coordinate system cs.
*)
let get_polyhedron_of_formula srk f cs =
  let f = match Formula.destruct srk f with
    | `And xs -> xs
    | `Tru -> []
    | `Atom _ -> [ f ]
    | _ -> failwith "formula is not convex polyhedron"
  in
  Polyhedron.of_implicant ~admit:true cs f
  |> Polyhedron.enum
  |> BatList.of_enum

(** From the vector representation of a linear inequality, get the coefficient
    of a symbol.
 *)
let get_coeff_of_symbol cs vec symbol =
  try 
    let tid = CoordinateSystem.cs_term_id cs (`App (symbol, [])) in
    Vec.coeff tid vec
  with Not_found -> QQ.zero

(** Extracting linear terms that are non-increasing through one iteration.
    Let X, X' be the sets of pre- and post-transition variables. 
    Assume we have a convex polyhedron where variables range over X and X',
    according to Farkas' lemma, every function of the form 
    a(x - x') + b(y - y') >= 0 must be non-negative combinations of the 
    half-spaces that consitute the boundaries of the polyhedron.
    cs: coordinate system
    ineqs: inequalities as list of vectors
    dx_list: list of delta symbols defined using dx = x' - x for every x
    coeff_x_list: a list of symbolic coefficients in the final linear terms
    coeff_x_set: set of symbolic coefficients
*)
let build_system_of_ineq_for_non_inc srk cs ineqs dx_list coeff_x_list coeff_x_set =
  (* first create the lambda symbols for each inequality and set that they are non-negative *)
  let lambdas, f_with_non_neg_lambdas = 
    BatList.fold_righti
      (fun i ineq (lambdas, f) ->
         let lambda_i_name = String.concat "_" ["lambda"; string_of_int i] in
         let lambda_i = mk_const srk (mk_symbol srk ~name:lambda_i_name `TyReal) in
         match ineq with
         | `LeqZero _ ->
           begin
             let newf = mk_and srk [mk_leq srk (mk_zero srk) lambda_i;  f] in
             (List.cons (lambda_i, lambda_i) lambdas, newf)
           end
         | `LtZero _ -> failwith "expecting non-strict ineqs"
         | `EqZero _ -> 
           begin
             let lambda_ip_name = String.concat "_" ["lambda"; "neg"; string_of_int i] in
             let lambda_ip = mk_const srk (mk_symbol srk ~name:lambda_ip_name `TyReal) in
             let newf1 = mk_and srk [mk_leq srk (mk_zero srk) lambda_i; f] in
             let newf2 = mk_and srk [mk_leq srk (mk_zero srk) lambda_ip; newf1] in
             (List.cons (lambda_i, lambda_ip) lambdas, newf2)
           end
      )
      ineqs
      ([], mk_true srk)
  in
  (** then add the coefficient constraints to the system: for each variable,
      linear combination of its coefficient within each inequality results in  
      the final coefficients of this variable in the final linear term
   *)
  let answer =
    BatList.fold_lefti
      (fun formulas i sym -> 
         let full_rhs =
           BatList.fold_lefti 
             (fun rhs i ineq ->
                match ineq with
                | `LeqZero t ->
                  begin
                    let lambda_i, _ = List.nth lambdas i in
                    let coeff = get_coeff_of_symbol cs t sym in
                    mk_add srk [rhs; mk_mul srk [lambda_i; mk_real srk coeff] ]
                  end
                | `LtZero _ -> failwith "expecting non-strict ineqs"
                | `EqZero t -> 
                  begin
                    let coeff = get_coeff_of_symbol cs t sym in
                    let lambda_i, lambda_ip = List.nth lambdas i in
                    mk_add srk [rhs; 
                                mk_mul srk [lambda_i; mk_real srk coeff];
                                mk_mul srk [lambda_ip; mk_neg srk (mk_real srk coeff)] ]
                  end
             )
             (mk_zero srk)
             ineqs
         in
         let coeff_sym = List.nth coeff_x_list i in
         let equ_for_this_var = mk_eq srk (mk_const srk coeff_sym) full_rhs in
         mk_and srk [ equ_for_this_var ; formulas]
      )
      f_with_non_neg_lambdas
      dx_list
  in
  logf "\nformula of lambdas on non-inc:\n%s\n\n" (Formula.show srk answer);
  (* finally add the constant constraints such that the final linear term is non-positive *)
  let formula_with_const_constraints = 
    let rhs =
      BatList.fold_lefti
        (fun term i ineq ->
           match ineq with
           | `LeqZero t ->
             begin
               let c = Vec.coeff CoordinateSystem.const_id t in
               let lambda_i, _ = List.nth lambdas i in
               mk_add srk [mk_mul srk [mk_real srk c; lambda_i]; term]
             end
           | `LtZero _ -> failwith "expecting non-strict ineqs"
           | `EqZero t -> 
             begin
               let c = Vec.coeff CoordinateSystem.const_id t in
               let lambda_i, lambda_ip = List.nth lambdas i in
               mk_add srk [mk_mul srk [mk_real srk c; lambda_i]; 
                           mk_mul srk [mk_neg srk (mk_real srk c); lambda_ip]; term]
             end
        )
        (mk_zero srk)
        ineqs
    in
    mk_and srk [answer; mk_leq srk (mk_zero srk) rhs]
  in
  logf "\nfinal formula for non-inc:\n%s\n" (Formula.show srk formula_with_const_constraints);
  let polka = Polka.manager_alloc_strict () in
  let f = rewrite srk ~down:(nnf_rewriter srk) formula_with_const_constraints in
  let property_of_formula =
    let exists x = Symbol.Set.mem x coeff_x_set in
    Abstract.abstract ~exists:exists srk polka f
  in
  let resulting_formula = SrkApron.formula_of_property property_of_formula in
  logf "\n non-inc cone:\n%s\n" (Formula.show srk resulting_formula);
  property_of_formula

(** The linear terms that are non-increasing form a cone. Here we actually compute
    the generator representation of the cone.
    formula: the formula from which we extract non-increasing linear terms
    dx_list: list of delta symbols
    dx_set: set of delta symbols
    coeff_x_list: list containing symbolic coefficients of each variable in the final term
    coeff_x_set: set of symbolic coefficients for easy look up
*)
let compute_non_inc_term_cone srk formula dx_list dx_set coeff_x_list coeff_x_set  =
  let polka = Polka.manager_alloc_strict () in
  let f = rewrite srk ~down:(nnf_rewriter srk) formula in
  let property_of_dx =
    let exists x = Symbol.Set.mem x dx_set in
    Abstract.abstract ~exists:exists srk polka f
  in
  let formula_of_dx = SrkApron.formula_of_property property_of_dx in
  logf "\nformula on dx:\n%s\n" (Formula.show srk formula_of_dx);
  let cs = CoordinateSystem.mk_empty srk in
  let ineqs = get_polyhedron_of_formula srk formula_of_dx cs in
  let non_inc_cone = build_system_of_ineq_for_non_inc srk cs ineqs dx_list coeff_x_list coeff_x_set in
  non_inc_cone, cs

(** Similar to build_system_of_ineq_for_non_inc method, this method computes
    linear terms over pre-transition variables that are guaranteed to be 
    bounded from below.
    cs: coordinate system
    ineqs: inequalities as list of vectors
    x_list: list of variable symbols
    coeff_x_list: a list of symbolic coefficients in the final linear terms
    coeff_x_set: set of symbolic coefficients
    TODO: extract common logic into dual cone computation into polyhedron.ml
*)
let build_system_of_ineq_for_lb_terms srk cs ineqs x_list coeff_x_list coeff_x_set =
  (* first create the lambda symbols for each inequality *)
  let lambdas, f_with_non_neg_lambdas = 
    BatList.fold_righti
      (fun i ineq (lambdas, f) ->
         let lambda_i_name = String.concat "_" ["lambda"; string_of_int i] in
         let lambda_i = mk_const srk (mk_symbol srk ~name:lambda_i_name `TyReal) in
         match ineq with
         | `LeqZero _ ->
           begin
             let newf = mk_and srk [mk_leq srk (mk_zero srk) lambda_i;  f] in
             (List.cons (lambda_i, lambda_i) lambdas, newf)
           end
         | `LtZero _ -> failwith "expecting non-strict ineqs"
         | `EqZero _ -> 
           begin
             let lambda_ip_name = String.concat "_" ["lambda"; "neg"; string_of_int i] in
             let lambda_ip = mk_const srk (mk_symbol srk ~name:lambda_ip_name `TyReal) in
             let newf1 = mk_and srk [mk_leq srk (mk_zero srk) lambda_i; f] in
             let newf2 = mk_and srk [mk_leq srk (mk_zero srk) lambda_ip; newf1] in
             (List.cons (lambda_i, lambda_ip) lambdas, newf2)
           end
      )
      ineqs
      ([], mk_true srk)
  in
  (* then add the coefficient constraints to the system, note this is slightly
      different than above
   *)
  let answer =
    BatList.fold_lefti
      (fun formulas i sym -> 
         let full_rhs =
           BatList.fold_lefti 
             (fun rhs i ineq ->
                match ineq with
                | `LeqZero t ->
                  begin
                    let lambda_i, _ = List.nth lambdas i in
                    let coeff = QQ.negate (get_coeff_of_symbol cs t sym) in
                    mk_add srk [rhs; mk_mul srk [lambda_i; mk_real srk coeff] ]
                  end
                | `LtZero _ -> failwith "expecting non-strict ineqs"
                | `EqZero t -> 
                  begin
                    let coeff = QQ.negate (get_coeff_of_symbol cs t sym) in
                    let lambda_i, lambda_ip = List.nth lambdas i in
                    mk_add srk [rhs; 
                                mk_mul srk [lambda_i; mk_real srk coeff];
                                mk_mul srk [lambda_ip; mk_neg srk (mk_real srk coeff)] ]
                  end
             )
             (mk_zero srk)
             ineqs
         in
         let coeff_sym = List.nth coeff_x_list i in
         let equ_for_this_var = mk_eq srk (mk_const srk coeff_sym) full_rhs in
         mk_and srk [ equ_for_this_var ; formulas]
      )
      f_with_non_neg_lambdas
      x_list
  in
  logf "\nformula of lambdas for lb:\n%s\n" (Formula.show srk answer);
  let polka = Polka.manager_alloc_strict () in
  let f = rewrite srk ~down:(nnf_rewriter srk) answer in
  let property_of_formula =
    let exists x = Symbol.Set.mem x coeff_x_set in
    Abstract.abstract ~exists:exists srk polka f
  in
  let resulting_formula = SrkApron.formula_of_property property_of_formula in
  logf "\nlower-bounded cone:\n%s\n" (Formula.show srk resulting_formula);
  property_of_formula

(** The linear terms that are bound from below also form a cone. 
    formula: the formula from which we extract bound-from-below linear terms
    x_list: list of variable symbols
    x_set: set of variable symbols
    coeff_x_list: list containing symbolic coefficients of each variable in the final term
    coeff_x_set: set of symbolic coefficients for easy look up
*)
let compute_lower_bound_term_cone srk cs formula x_list x_set coeff_x_list coeff_x_set =
  let polka = Polka.manager_alloc_strict () in
  let f = rewrite srk ~down:(nnf_rewriter srk) formula in
  let property_of_dx =
    let exists x = Symbol.Set.mem x x_set in
    Abstract.abstract ~exists:exists srk polka f
  in
  let formula_of_lbx = SrkApron.formula_of_property property_of_dx in
  logf "\nformula of lower-bounded terms:\n%s\n\n" (Formula.show srk formula_of_lbx);
  let ineqs = get_polyhedron_of_formula srk formula_of_lbx cs in
  let non_inc_cone = build_system_of_ineq_for_lb_terms srk cs ineqs x_list coeff_x_list coeff_x_set in
  non_inc_cone

(** Compute quasi-ranking functions for formula f at a certain depth.
    This is done by intersecting the two cones at each depth, and then constraining
    the formula by dictating that the term for generators of the
    intersection has to stay the same, then recurse to the next depth with the 
    residual formula.
    depth: we are currently synthesizing the depth-th component of a lexicographic ranking function
    qrfs: quasi ranking functions
    x_list, xp_list, x_set, xp_set: list/set of pre- and post-transition symbols
    dx_set: set of delta symbols
    x_to_dx, dx_to_x: get the corresponding delta symbol for a variable symbol and vice versa
    coeff_x_list: list containing symbolic coefficients of each variable in the final term
    coeff_x_set: set of symbolic coefficients for easy look up
*) 
let rec find_quasi_rf depth srk f qrfs x_list xp_list dx_list x_set xp_set dx_set x_to_dx dx_to_x coeff_x_list coeff_x_set =
  let formula = f in
  let non_inc_term_cone, cs = compute_non_inc_term_cone srk formula dx_list dx_set coeff_x_list coeff_x_set in
  if (SrkApron.is_bottom non_inc_term_cone) then 
    begin
      logf ~attributes:[`Bold; `Red] "non-increasing term cone is empty, fail";
      (false, depth-1, formula, qrfs) 
    end
  else
    let lb_term_cone = compute_lower_bound_term_cone srk cs formula x_list x_set coeff_x_list coeff_x_set in
    if (SrkApron.is_bottom lb_term_cone) then 
      begin
        logf ~attributes:[`Bold; `Red] "bounded-term cone is empty, fail";
        (false, depth-1,formula, qrfs) 
      end
    else
      let c = SrkApron.meet non_inc_term_cone lb_term_cone in
      if (SrkApron.is_bottom c) then
        begin
          logf ~attributes:[`Bold; `Red] "intersection of two cones is empty, fail";
          (false, depth-1, formula, qrfs) 
        end
      else
        let gens = SrkApron.generators c in
        let coeff_all_zero = not (BatList.exists (fun (_, typ) -> match typ with | `Ray | `Line -> true | _ -> false) gens) in
        if coeff_all_zero then 
          begin
            logf ~attributes:[`Bold; `Red] "only all zero quasi ranking function exists at this level, fail";
            (false, depth-1, formula, qrfs) 
          end
        else
          let resulting_cone = SrkApron.formula_of_property c in
          logf "\ncone of qrfs:\n%s\n\n" (Formula.show srk resulting_cone);

          let get_orig_or_primed_expr_of_gen generator xs =
            let term = Linear.term_of_vec srk (
                fun d -> 
                  let coeffSym = symbol_of_int d in 
                  let origSym = List.nth 
                      xs 
                      (let ind, _ = BatList.findi (fun _ a -> a = coeffSym) coeff_x_list in ind)
                  in
                  mk_const srk origSym
              )
                generator in
            term
          in
          let new_qrfs = 
            (BatList.map 
               (fun (generator, _) ->
                  get_orig_or_primed_expr_of_gen generator x_list
               )
               gens) :: qrfs
          in
          let new_constraints = 
            BatList.map 
              (fun (generator, _) ->
                 let pre_trans_term = get_orig_or_primed_expr_of_gen generator x_list in
                 let post_trans_term = get_orig_or_primed_expr_of_gen generator xp_list in
                 let equ = mk_eq srk post_trans_term pre_trans_term in
                 equ
              )
              gens
          in
          let restricted_formula = mk_and srk (f :: new_constraints) in
          logf "\nrestricted formula for next iter:\n%s\n\n" (Formula.show srk restricted_formula);
          match Smt.equiv srk formula restricted_formula with
          | `Unknown -> logf ~attributes:[`Bold; `Red] "Cannot decide if there is any improvement at this level"; (false, depth, formula, qrfs)
          | `Yes -> logf ~attributes:[`Bold; `Red] "No improvement at this level, halt LLRF synthesis"; (false, depth, formula, qrfs)
          | `No -> logf ~attributes:[`Bold; `Green] "There is improvement at this level";
              match Smt.get_model srk restricted_formula with
              | `Sat _ -> 
                logf ~attributes:[`Bold; `Yellow] "\n\n\nTransition formula SAT, try to synthesize next depth\n\n";
                find_quasi_rf (depth+1) srk restricted_formula new_qrfs x_list xp_list dx_list x_set xp_set dx_set x_to_dx dx_to_x coeff_x_list coeff_x_set
              | `Unknown -> failwith "SMT solver should not return unknown"
              | `Unsat -> (logf ~attributes:[`Bold; `Green] "Transition formula UNSAT, done"); (true, depth, formula, qrfs)

(** This is a utility function that creates the delta symbols for each variable symbol,
    and relates the delta symbols with the original variable symbols by saying
    that each dx = x' - x.
*)
let add_diff_terms_to_formula srk f x_xp =
  List.fold_right
    (fun (x, xp) (f, dx_list, dx_sym_set, x_to_dx, dx_to_x) -> 
       let dname = String.concat "" ["d_"; show_symbol srk x] in
       let cx = mk_const srk x in
       let cxp = mk_const srk xp in 
       let diff = mk_sub srk cxp cx in
       let dx_sym = mk_symbol srk ~name:dname `TyInt in
       let dx = mk_const srk dx_sym in
       let f_with_dx = mk_and srk [f ; mk_eq srk dx diff] in
       (f_with_dx, 
        List.cons dx_sym dx_list,
        Symbol.Set.add dx_sym dx_sym_set, 
        Symbol.Map.add x dx_sym x_to_dx, 
        Symbol.Map.add dx_sym x dx_to_x)
    )
    x_xp
    (f, [], Symbol.Set.empty, Symbol.Map.empty, Symbol.Map.empty)

(* let simplify_residual_formula srk x_set xp_set residual_formula = 
  let polka = Polka.manager_alloc_strict () in
  let exists = fun x -> (Symbol.Set.mem x x_set || Symbol.Set.mem x xp_set) in
  Abstract.abstract ~exists:exists srk polka residual_formula
  |> SrkApron.formula_of_property *)
(** The actual swf operator only has true or false as outcomes, corresponding to
    able to prove or unable to prove results given here.
 *)
let compute_swf srk tf =
  let tf = TF.linearize srk tf in
  let all_symbols = Symbol.Set.to_list (symbols (TF.formula tf)) in
  let constant_symbols = List.filter (TF.is_symbolic_constant tf) all_symbols in
  let x_xp =
    List.fold_left (fun l s -> (s, s) :: l) (TF.symbols tf) constant_symbols
  in
  match Smt.get_model srk (TF.formula tf) with
  | `Sat _ -> 
    let x_list = List.fold_right (fun (sp, _) l -> sp :: l ) x_xp [] in
    let xp_list = List.fold_right (fun (_, spp) l -> spp :: l ) x_xp [] in
    let coeff_x_list, coeff_x_set = 
      List.fold_right 
        (fun x (l, s) ->
           let coeff_sym = mk_symbol srk ~name:(String.concat "_" ["coeff"; show_symbol srk x]) `TyReal in
           (coeff_sym :: l, Symbol.Set.add coeff_sym s)
        )
        x_list
        ([], Symbol.Set.empty)
    in
    let x_set = TF.pre_symbols x_xp in
    let xp_set = TF.post_symbols x_xp in
    let f_with_dx, dx_list, dx_set, x_to_dx, dx_to_x =
      add_diff_terms_to_formula srk (TF.formula tf) x_xp
    in
    logf "\nformula with dx:\n%s\n" (Formula.show srk f_with_dx);
    let (success, dep, residual_formula, _) =
      find_quasi_rf 1 srk f_with_dx [] x_list xp_list dx_list x_set xp_set dx_set x_to_dx dx_to_x coeff_x_list coeff_x_set
    in
    logf "\nSuccess: %s\nDepth: %s\n" (string_of_bool success) (string_of_int dep);
    if success then (ProvedToTerminate, mk_false srk) else (Unknown, residual_formula)
  | `Unknown -> logf "SMT solver should not return unknown for QRA formulas"; (Unknown, mk_true srk)
  | `Unsat -> (logf ~attributes:[`Bold; `Yellow] "Transition formula UNSAT, done"); (ProvedToTerminate, mk_false srk)

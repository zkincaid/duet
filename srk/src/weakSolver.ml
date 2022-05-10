open Syntax
open BatPervasives

module V = Linear.QQVector
module Monomial = Polynomial.Monomial
module P = Polynomial.QQXs
module Scalar = Apron.Scalar
module Coeff = Apron.Coeff
module Abstract0 = Apron.Abstract0
module Linexpr0 = Apron.Linexpr0
module Lincons0 = Apron.Lincons0
module Dim = Apron.Dim

module CS = CoordinateSystem

module IntSet = SrkUtil.Int.Set

include Log.Make(struct let name = "srk.weaksolver" end)

let pp_dim srk = (fun formatter i -> Format.fprintf formatter "%a" (pp_symbol srk) (symbol_of_int i))

let rec get_quantifiers srk env phi =
  let phi = Formula.prenex srk phi in
  match Formula.destruct srk phi with
  | `Quantify (qt, name, typ, psi) ->
    let k = mk_symbol srk ~name (typ :> Syntax.typ) in
    let (qf_pre, psi) = get_quantifiers srk (Env.push k env) psi in
    ((qt,k)::qf_pre, psi)
  | _ -> ([], substitute srk (fun (i, _) -> mk_const srk (Env.find env i)) phi)

(* TODO: implement an incremental solver, that retains a solver object and nonlinear map.
The current get_model just takes in a solver object which contains phi and nonlinear map. *)
(* Get a weak theory model for a formula. Also serves as an SMT solver for weak theory. *)
let get_model srk phi =
  Z3.set_global_param "model.completion" "true";
  let phi = eliminate_ite srk phi in
  let phi = SrkSimplify.simplify_terms srk phi in
  (* Get the quantifiers and the ground formula. The weak theory only supports existentials. *)
  let quantifiers, phi = get_quantifiers srk Env.empty phi in

  logf "getting model for formula: %a" (Formula.pp srk) phi;
  let phi = Nonlinear.eliminate_floor_mod_div srk phi in
  let phi = SrkSimplify.simplify_terms srk phi in
  logf "weakSolver: eliminated floor, mod, div: %a" (Formula.pp srk) phi;

  assert (BatList.for_all (fun quant -> match quant with `Exists, _ -> true | _ -> false)
            quantifiers = true);
  (* QF_LRA, QF_UF *)
  let solver = Smt.mk_solver ~theory:"QF_LIRA" srk in

  let declared_ints =
    Symbol.Set.fold
      (fun sym l ->
        match Syntax.typ_symbol srk sym with
        | `TyInt ->
           (* logf ~level:`trace "%s : fun" (Syntax.show_symbol srk sym); *)
           (sym :: l)
        | `TyReal
          | `TyBool
          | `TyArr -> l
        | `TyFun (_args, _range_typ) ->
           (* if args = [] && range_typ = `TyInt then
             (sym :: l)
           else *)
           l
      )
      (Syntax.symbols phi)
      []
  in

  let new_is_ints =
    List.map
      (fun sym ->
        Syntax.mk_const srk sym
        |> Syntax.ArithTerm.arith_term_of srk
        |> mk_is_int srk)
      declared_ints in
  let phi_with_ints = Syntax.mk_and srk (phi :: new_is_ints) in
  logf "weakSolver: added is_ints: %a" (Formula.pp srk) phi_with_ints;

  let (prop_skeleton, unprop_map) =
    rewrite srk
      ~down:(nnf_rewriter_without_replacing_eq srk)
      phi_with_ints
    |> SrkSimplify.propositionalize srk
  in
  let unprop fml =
    Syntax.substitute_const srk
      (fun sym ->
        try
          Symbol.Map.find sym unprop_map
        with Not_found ->
          Syntax.mk_const srk sym
      )
      fml
  in
  logf ~level:`trace "weakSolver: unprop_map: @[%a@]"
    (fun _fmt unprop_map ->
      BatEnum.iter (fun (sym, expr) ->
          logf "(%a, %a)@;" (Syntax.pp_symbol srk) sym (Syntax.Expr.pp srk) expr)
        (Symbol.Map.enum unprop_map))
    unprop_map;

  Smt.Solver.add solver [prop_skeleton];

  (* TODO: adding lemmas. Using preduce in Groebner basis to get a subset of
     atoms whose conjunction is unsat. *)
  let rec go () =
    logf ~level:`trace "weakSolver: solver is: %s ===" (Smt.Solver.to_string solver);
    match Smt.Solver.get_model solver with
    | `Unsat -> `Unsat
    | `Unknown -> `Unknown
    | `Sat model ->
       logf ~level:`trace "weakSolver: successfully getting model";
    (* match Interpretation.select_implicant model lin_phi with *)
       match Interpretation.select_implicant model prop_skeleton with
       | None -> assert false
       | Some implicant ->
          logf ~level:`trace "weakSolver: got implicant";
          let () = BatList.iter (fun f ->
                       logf ~level:`trace "weakSolver: Selected implicant atom: %a"
                         (Formula.pp srk) f) implicant in
          (* The implicant should be atomic, should be able to destruct to get t < c, t <= c, t = c *)
          (* let implicant = List.map (fun imp -> replace_defs imp) implicant in *)
          logf ~level:`trace "weakSolver: Unpropping...";
          let atoms = List.map unprop implicant in
          logf ~level:`trace "weakSolver: Unpropped";

          let rec process_atoms l geqs eqs ineqs lat_members lat_nonmembers =
            match l with
            | [] -> logf ~level:`trace "weakSolver: list of atoms left is empty";
                    (geqs, eqs, ineqs, lat_members, lat_nonmembers)
            | h :: t ->
               logf ~level:`trace "weakSolver: Processing atom: %a" (Formula.pp srk) h;
               match (Interpretation.destruct_atom_for_weak_theory srk h) with
                 `ArithComparisonWeak (`Eq, a, b) ->
                  process_atoms t geqs ((mk_sub srk a b) :: eqs) ineqs lat_members lat_nonmembers
               | `ArithComparisonWeak (`Neq, a, b) ->
                  let diff = mk_sub srk a b in
                  process_atoms t geqs eqs (diff :: ineqs) lat_members lat_nonmembers
               | `ArithComparisonWeak (`Leq, a, b) ->
                  process_atoms t ((mk_sub srk b a) :: geqs) eqs ineqs lat_members lat_nonmembers
               | `ArithComparisonWeak (`Lt, a, b) ->
                  (* Strict inequality a < b is represented as a <= b && a != b. *)
                  let diff = mk_sub srk b a in
                  process_atoms t (diff :: geqs) eqs (diff :: ineqs) lat_members lat_nonmembers
               | `IsInt (sign, s) when sign = `Pos ->
                  process_atoms t geqs eqs ineqs (s :: lat_members) lat_nonmembers
               | `IsInt (sign, s) when sign = `Neg ->
                  process_atoms t geqs eqs ineqs lat_members (s :: lat_nonmembers)
               | `Literal _ -> process_atoms t geqs eqs ineqs lat_members lat_nonmembers
               | _ -> failwith "Weak theory does not support arr expressions."
          in
          let geqs, eqs, ineqs2, lat_members, lat_nonmembers =
            process_atoms atoms [] [] [] [] [] in
          let geqs = BatList.map (fun expr -> P.of_term srk expr) geqs in
          let eqs = BatList.map (fun expr -> P.of_term srk expr) eqs in
          let ineqs = BatList.map (fun expr -> P.of_term srk expr) ineqs2 in
          let is_ints = BatList.map (fun expr -> P.of_term srk expr) lat_members in
          let not_ints = BatList.map (fun expr -> P.of_term srk expr) lat_nonmembers in
          BatList.iter
            (fun f -> logf ~level:`trace "weakSolver: checking inequations: %a"
                        (Syntax.ArithTerm.pp srk) f)
            ineqs2;
          let initial_ideal =
            Polynomial.Rewrite.mk_rewrite Polynomial.Monomial.degrevlex eqs
            |> Polynomial.Rewrite.grobner_basis
          in
          logf ~level:`trace
            "weakSolver: Start making enclosing cone of: ideal: @[%a@] @; geqs: @[%a@]"
            (Polynomial.Rewrite.pp (pp_dim srk))
            initial_ideal
            (PolynomialUtil.PrettyPrint.pp_poly_list (pp_dim srk))
            geqs;

          let pc = PolynomialCone.make_enclosing_cone initial_ideal geqs in
          let lattice = PolynomialConeCpClosure.polylattice_spanned_by is_ints in

          (* NK: TODO: This triggers a bug that corrupts memory, e.g., the lattice. *)
          logf
            "weakSolver: lattice: @[%a@],@;  initially generated by @[%a@]@;"
            (PolynomialConeCpClosure.pp_polylattice (pp_dim srk))
            lattice
            (PolynomialUtil.PrettyPrint.pp_poly_list (pp_dim srk))
            is_ints;

          logf "weakSolver: enclosing cone: @[%a@]"
            (PolynomialCone.pp (pp_dim srk)) pc;

          let continue () =
            let f = (mk_not srk (mk_and srk implicant)) in
            logf "weakSolver: adding formula to solver: %a" (Formula.pp srk) f;
            Smt.Solver.add solver [f]; go ()
          in

          let contradict_int =
            (* The IsInt relation is not closed under equality, so this is all we have
               to check.
             *)
            List.exists (fun p -> PolynomialConeCpClosure.in_polylattice p lattice)
              not_ints
          in
          if contradict_int then
            continue ()
          else
            let cut_pc = PolynomialConeCpClosure.regular_cutting_plane_closure lattice pc in
            logf ~level:`trace "weakSolver: Finish making enclosing cone";
            (* Check if induced equalities contradict with strict inequalities
             as required by the formula.  *)
            let ideal = PolynomialCone.get_ideal cut_pc in
            let contradict_inequations =
              BatList.exists (fun nonzero ->
                  let t = Polynomial.Rewrite.reduce ideal nonzero in
                  Polynomial.QQXs.equal t Polynomial.QQXs.zero
                ) ineqs in
            logf "weakSolver: Strict inequations cannot be satisfied: %b" contradict_inequations;

            (* If the polynomial cone is not proper then the model is no longer consistent. *)
            if (PolynomialCone.is_proper cut_pc)
               && not contradict_inequations && not contradict_int then
              let () = logf "weakSolver: Got a model represented as polynomial cone: %a"
                         (PolynomialCone.pp (pp_dim srk)) cut_pc in
              `Sat (model, cut_pc)
            else continue ()
  in
  go ()

let is_sat srk phi =
  match get_model srk phi with
    `Sat _ -> `Sat
  | `Unsat -> `Unsat
  | `Unknown -> `Unknown

(* projecting down to only linear consequences distributes through intersection, so could
   do project first then compute intersection, which could be cheaper *)

(* Finding all equations and inequalities implied by a formula according to the weak theory. *)
let find_consequences srk orig_phi =
  let phi_symbols = Syntax.symbols orig_phi in
  let phi = eliminate_ite srk orig_phi in
  let phi = SrkSimplify.simplify_terms srk phi in
  let quantifiers, phi = get_quantifiers srk Env.empty phi in
  logf "Finding consequences for formula: %a" (Formula.pp srk) phi;
  assert (BatList.for_all (fun quant -> match quant with `Exists, _ -> true | _ -> false) quantifiers = true);
  (* let existential_vars = BatSet.of_list *)
  (*     (BatList.filter_map *)
  (*        (fun quant -> match quant with `Exists, x -> logf "exists %a" (Syntax.pp_symbol srk) x; Some x | _ -> None) *)
  (*        quantifiers) *)
  (* in *)
  let pc = PolynomialCone.trivial in
  let rec go current_pc formula =
    (* logf "current formula: %a" (Formula.pp srk) formula; *)
    logf "getting model in find conseq";
    match get_model srk formula with
      `Sat (_, poly_cone) ->
      begin
        logf "got model poly cone: %a" (PolynomialCone.pp (pp_dim srk)) poly_cone;
        (* let existential_vars = BatList.fold (fun s sym -> BatSet.add sym s) existential_vars new_symbols in *)
        let projected_pc = PolynomialCone.project
            poly_cone
            (fun i -> let s =  Syntax.symbol_of_int i in Syntax.Symbol.Set.mem s phi_symbols)
        in
        logf "projected poly cone: %a" (PolynomialCone.pp (pp_dim srk)) projected_pc;
        let new_pc = PolynomialCone.intersection current_pc projected_pc in
        logf "intersection: %a" (PolynomialCone.pp (pp_dim srk)) new_pc;
        let term_of_dim dim = mk_const srk (symbol_of_int dim) in
        let blocking_clause = PolynomialCone.to_formula srk term_of_dim new_pc |> mk_not srk in
        (* logf "adding blocking clause: %a" (Formula.pp srk) blocking_clause; *)
        let augmented_formula = mk_and srk [formula; blocking_clause] in
        go new_pc augmented_formula
      end
    | `Unsat -> logf "Found consequence: %a" (PolynomialCone.pp (pp_dim srk)) current_pc; current_pc
    | `Unknown -> failwith "Cannot find a model for the current formula"
  in
  go pc phi

let filter_polys_linear_in_dims dims polys =
  let polys_linear_in_dx = BatList.filter_map
      (fun poly -> let lin, higher = Polynomial.QQXs.split_linear poly in
        let higher_contains_dx =
          BatEnum.exists
            (fun (_, mono) ->
               BatEnum.exists
                 (fun (dim, _) ->
                    if BatSet.Int.mem dim dims then
                      true
                    else false
                 )
                 (Polynomial.Monomial.enum mono)
            )
            (Polynomial.QQXs.enum higher)
        in
        if higher_contains_dx then None else Some (lin, higher)
      )
      polys
  in
  BatList.filter_map (fun (lin, higher) ->
      let linterm_of_only_dx_enum = BatEnum.filter_map (fun (coeff, dim) ->
          if BatSet.Int.mem dim dims then Some (coeff, dim) else None
        )
          (V.enum lin)
      in
      let linterm_of_only_dx = V.of_enum linterm_of_only_dx_enum in
      let p = Polynomial.QQXs.of_vec linterm_of_only_dx in
      let other_linterm = V.sub lin linterm_of_only_dx in
      let other_poly = Polynomial.QQXs.of_vec other_linterm in
      if V.is_zero linterm_of_only_dx then None else Some (P.add p (P.add other_poly higher))
    )
    polys_linear_in_dx

let project_down_to_linear pc lin_dims =
  let ideal = PolynomialCone.get_ideal pc in
  let ideal_gen = Polynomial.Rewrite.generators ideal in
  let lin_ideal = filter_polys_linear_in_dims lin_dims ideal_gen in
  (* let cone_gen = PolynomialCone.get_cone_generators pc in *)
  (* let lin_cone = filter_polys_linear_in_dims lin_dims cone_gen in *)
  let lin_cone = [] in
  let new_ideal = Polynomial.Rewrite.mk_rewrite (Polynomial.Rewrite.get_monomial_ordering ideal) lin_ideal in
  PolynomialCone.make_enclosing_cone new_ideal lin_cone

let find_linear_consequences srk phi lin_dims =
  let phi = eliminate_ite srk phi in
  let phi = SrkSimplify.simplify_terms srk phi in
  let quantifiers, phi = get_quantifiers srk Env.empty phi in
  logf "Finding consequences for formula: %a" (Formula.pp srk) phi;
  assert (BatList.for_all (fun quant -> match quant with `Exists, _ -> true | _ -> false) quantifiers = true);
  let existential_vars = BatSet.of_list
      (BatList.filter_map
         (fun quant -> match quant with `Exists, x -> logf "exists %a" (Syntax.pp_symbol srk) x; Some x | _ -> None)
         quantifiers)
  in
  let pc = PolynomialCone.trivial in
  let rec go current_pc formula =
    (* logf "current formula: %a" (Formula.pp srk) formula; *)
    logf "getting model in find conseq";
    match get_model srk formula with
      `Sat (_, poly_cone) ->
      begin
        logf "got model poly cone: %a" (PolynomialCone.pp (pp_dim srk)) poly_cone;
        let projected_pc = PolynomialCone.project
            poly_cone
            (fun i -> let s = Syntax.symbol_of_int i in not (BatSet.mem s existential_vars))
        in
        logf "projected poly cone: %a" (PolynomialCone.pp (pp_dim srk)) projected_pc;
        let projected_pc = project_down_to_linear projected_pc lin_dims in
        let new_pc = PolynomialCone.intersection current_pc projected_pc in
        let new_pc = project_down_to_linear new_pc lin_dims in
        logf "intersection: %a" (PolynomialCone.pp (pp_dim srk)) new_pc;
        let term_of_dim dim = mk_const srk (symbol_of_int dim) in
        let blocking_clause = PolynomialCone.to_formula srk term_of_dim new_pc |> mk_not srk in
        (* logf "adding blocking clause: %a" (Formula.pp srk) blocking_clause; *)
        let augmented_formula = mk_and srk [formula; blocking_clause] in
        go new_pc augmented_formula
      end
    | `Unsat ->
      logf "Found consequence: %a" (PolynomialCone.pp (pp_dim srk)) current_pc; current_pc
    | `Unknown -> failwith "Cannot find a model for the current formula"
  in
  go pc phi

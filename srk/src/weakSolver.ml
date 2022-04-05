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
  assert (BatList.for_all (fun quant -> match quant with `Exists, _ -> true | _ -> false) quantifiers = true);
  let solver = Smt.mk_solver ~theory:"QF_LIRA" srk in
  (* Special note: cannot rewrite into negation normal form past equalities, since
     not (p = 0) is not equiv to p > 0 or p < 0 in the weak theory *)
  let uninterp_phi =
    rewrite srk
      ~down:(nnf_rewriter_without_replacing_eq srk)
      ~up:(Nonlinear.uninterpret_rewriter srk)
      phi
  in
    (* logf "Uninterpreted formula: %a" (Formula.pp srk) uninterp_phi; *)
let (lin_phi, nonlinear) = SrkSimplify.purify srk uninterp_phi in
  let nonlinear_defs =
    Symbol.Map.enum nonlinear
    /@ (fun (symbol, expr) ->
        match Expr.refine srk expr with
        | `ArithTerm t -> mk_eq srk (mk_const srk symbol) t
        | `Formula phi -> mk_iff srk (mk_const srk symbol) phi
        | `ArrTerm _ -> assert false)
    |> BatList.of_enum
  in

  let rec replace_defs_term term =
    substitute_const
      srk
      (fun x ->
         try replace_defs_term (Symbol.Map.find x nonlinear)
         with Not_found -> mk_const srk x)
      term
  in
  let replace_defs =
    substitute_const
      srk
      (fun x ->
         try replace_defs_term (Symbol.Map.find x nonlinear)
         with Not_found -> mk_const srk x)
  in

  (* Smt.Solver.add solver [uninterp_phi]; *)
  Smt.Solver.add solver (lin_phi :: nonlinear_defs);

  (* TODO: adding lemmas. Using preduce in Groebner basis to get a subset of atoms whose conjunction is unsat. *)
  let rec go () =

    (* logf "solver is: %s ===" (Smt.Solver.to_string solver); *)
    match Smt.Solver.get_model solver with
    | `Unsat -> `Unsat
    | `Unknown -> `Unknown
    | `Sat model ->
      logf "successfully getting model";
      match Interpretation.select_implicant model lin_phi with
      | None -> assert false
      | Some implicant ->
        logf "got implicant";
        (* let () = BatList.iter (fun f -> *)
            (* logf "Selected implicant atom: %a" (Formula.pp srk) f) implicant in *)
        (* The implicant should be atomic, should be able to destruct to get t < c, t <= c, t = c *)
        let implicant = List.map (fun imp -> replace_defs imp) implicant in
        let atoms = List.map (Nonlinear.interpret srk) implicant in

        let rec process_atoms l geqs eqs ineqs =
          match l with
          | [] -> logf "list of atoms left is empty"; (geqs, eqs, ineqs)
          | h :: t ->
            logf "Processing atom: %a" (Formula.pp srk) h;
            match (Interpretation.destruct_atom_for_weak_theory srk h) with
              `ArithComparisonWeak (`Eq, a, b) ->
              process_atoms t geqs ((mk_sub srk a b) :: eqs) ineqs
            | `ArithComparisonWeak (`Neq, a, b) ->
              let diff = mk_sub srk a b in
              process_atoms t geqs eqs (diff :: ineqs)
            | `ArithComparisonWeak (`Leq, a, b) ->
              process_atoms t ((mk_sub srk b a) :: geqs) eqs ineqs
            | `ArithComparisonWeak (`Lt, a, b) ->
              (* Strict inequality a < b is represented as a <= b && a != b. *)
              let diff = mk_sub srk b a in
              process_atoms t (diff :: geqs) eqs (diff :: ineqs)
            | `Literal _ -> process_atoms t geqs eqs ineqs
            | _ -> failwith "Weak theory does not support arr expressions."
        in
        let geqs, eqs, ineqs2 = process_atoms atoms [] [] [] in
        let geqs = BatList.map (fun expr -> P.of_term srk expr) geqs in
        let eqs = BatList.map (fun expr -> P.of_term srk expr) eqs in
        let ineqs = BatList.map (fun expr -> P.of_term srk expr) ineqs2 in
        BatList.iter (fun f -> logf "checking inequalities: %a" (Syntax.ArithTerm.pp srk) f) ineqs2;
        let initial_ideal =
          Polynomial.Rewrite.mk_rewrite Polynomial.Monomial.degrevlex eqs
          |> Polynomial.Rewrite.grobner_basis
        in
        logf "Start making enclosing cone";
        let pc = PolynomialCone.make_enclosing_cone initial_ideal geqs in
        logf "Finish making enclosing cone";
        (* Check if induced equalities contradict with strict inequalities as required by the formula.  *)
        let contradictory = BatList.exists (fun nonzero -> let ideal = PolynomialCone.get_ideal pc in
                                             let t = Polynomial.Rewrite.reduce ideal nonzero in
                                             Polynomial.QQXs.equal t Polynomial.QQXs.zero
                                             ) ineqs in
        logf "Strict inequalities cannot be satisfied: %b" contradictory;
        (* If the polynomial cone is not proper then the model is no longer consistent. *)
        if (PolynomialCone.is_proper pc) && not contradictory then
          let () = logf "Got a model represented as polynomial cone: %a" (PolynomialCone.pp (pp_dim srk)) pc in
          `Sat (model, pc)
        else
          begin
            let f = (mk_not srk (mk_and srk implicant)) in
            logf "adding formula to solver: %a" (Formula.pp srk) f;
            Smt.Solver.add solver [f]; go ()
          end
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
let find_consequences srk phi =
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

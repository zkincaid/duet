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

let get_model srk phi =
  (* Use normalize in quantifier.ml to compute the prenex normal form and get the existentials *)
  let phi = eliminate_ite srk phi in
  let phi =
    SrkSimplify.simplify_terms srk phi
  in
  let quantifiers, phi = Quantifier.normalize srk phi in
  logf "formula: %a" (Formula.pp srk) phi;
  (* This module should be sound wrt the theory, other things like x > 0 <=> x >= 1 happen in other modules *)
  (* cannot rewrite into negation normal form past equalities, since
     not (p = 0) is not equiv to p > 0 or p < 0
     since don't have total order *)
  assert (BatList.for_all (fun quant -> match quant with `Exists, _ -> true | _ -> false) quantifiers = true);

  let solver = Smt.mk_solver ~theory:"QF_LIRA" srk in
  let uninterp_phi =
    rewrite srk
      ~down:(nnf_rewriter srk)
      ~up:(Nonlinear.uninterpret_rewriter srk)
      phi
  in
  logf "Uninterpreted formula: %a" (Formula.pp srk) uninterp_phi;
  (* nonlinear is a map from symbols to term/formula *)
  let (lin_phi, nonlinear) = SrkSimplify.purify srk uninterp_phi in
  logf "Linear formula skeleton: %a" (Formula.pp srk) lin_phi;
  (* Creating a list of relationships between symbols and their meanings *)
  let nonlinear_defs =
    Symbol.Map.enum nonlinear
    /@ (fun (symbol, expr) ->
        match Expr.refine srk expr with
        | `ArithTerm t -> mk_eq srk (mk_const srk symbol) t
        | `ArrTerm _ -> failwith "Weak solver does not support ArrTerm"
        | `Formula phi -> mk_iff srk (mk_const srk symbol) phi)
    |> BatList.of_enum
  in
  let nonlinear = Symbol.Map.map (Nonlinear.interpret srk) nonlinear in
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
  Smt.Solver.add solver [lin_phi];
  Smt.Solver.add solver nonlinear_defs;

  (* TODO: adding lemmas. Using preduce in Groebner basis to get a subset of atoms whose conjunction is unsat. *)
   let rec go () =
    match Smt.Solver.get_model solver with
    | `Unsat -> `Unsat
    | `Unknown -> `Unknown
    | `Sat model ->
      match Interpretation.select_implicant model lin_phi with
      | None -> assert false
      | Some implicant ->
        (* The formulas should be atoms, should be able to destruct to get t < c, t <= c, t = c *)
        let atoms = List.map replace_defs implicant in
        let rec process_atoms l geqs eqs ineqs =
          match l with
          | [] -> (geqs, eqs, ineqs)
          | h :: t ->
              logf "Processing atom: %a" (Formula.pp srk) h;
              match (Interpretation.destruct_atom srk h) with
              `ArithComparison (`Eq, a, b) ->
              process_atoms t geqs ((mk_sub srk a b) :: eqs) ineqs
            | `ArithComparison (`Leq, a, b) ->
              process_atoms t ((mk_sub srk b a) :: geqs) eqs ineqs
            | `ArithComparison (`Lt, a, b) ->
              (* Handle disequations using polynomial cone membership *)
              let diff = mk_sub srk b a in
              process_atoms t (diff :: geqs) eqs (diff :: ineqs)
            | `Literal _ -> process_atoms t geqs eqs ineqs
            | _ -> failwith "Weak theory does not support arr expressions."
        in
        let geqs, eqs, ineqs = process_atoms atoms [] [] [] in
        let geqs = BatList.map (fun expr -> P.of_term srk expr) geqs in
        let eqs = BatList.map (fun expr -> P.of_term srk expr) eqs in
        let ineqs = BatList.map (fun expr -> P.of_term srk expr) ineqs in
        let initial_ideal = Polynomial.Ideal.make eqs in
        logf "Start making enclosing cone";
        let pc = PolynomialCone.make_enclosing_cone initial_ideal geqs in
        logf "Finish making enclosing cone";
        (* Check if induced equalities contradict with strict inequalities appeared in the formula  *)
        let contradictory = BatList.exists (fun nonzero -> PolynomialCone.mem (P.negate nonzero) pc) ineqs in
        (* If the polynomial cone is not proper then the model is no longer consistent *)
        if (PolynomialCone.is_proper pc) && not contradictory then `Sat (model, pc)
        else
          begin
            Smt.Solver.add solver [(mk_not srk (mk_and srk implicant))]; go ()
          end
  in
  if Symbol.Map.is_empty nonlinear then
    match Smt.Solver.get_model solver with
      `Sat model -> `Sat (model, PolynomialCone.empty)
    | `Unsat -> `Unsat
    | `Unknown -> `Unknown
  else
    go ()

let is_sat srk phi =
  match get_model srk phi with
    `Sat _ -> `Sat
  | `Unsat -> `Unsat
  | `Unknown -> `Unknown

(* Finding all implied equations and equalities within the weak theory.  *)
let find_consequences srk phi =
   let phi = eliminate_ite srk phi in
  let phi =
    SrkSimplify.simplify_terms srk phi
  in
  let quantifiers, phi = Quantifier.normalize srk phi in
  logf "formula: %a" (Formula.pp srk) phi;
  assert (BatList.for_all (fun quant -> match quant with `Exists, _ -> true | _ -> false) quantifiers = true);
  let existential_vars = BatSet.of_list
      (BatList.filter_map (fun quant -> match quant with `Exists, x -> Some x | _ -> None) quantifiers)
  in
  let pc = PolynomialCone.empty in
  let term_of_int = fun i ->
    let s = symbol_of_int i in
    mk_const srk s
  in
  let rec go current_pc formula =
    match get_model srk formula with
      `Sat (_, poly_cone) ->
      begin
        let projected_pc = PolynomialCone.project
            poly_cone
            (fun i -> let s = Syntax.symbol_of_int i in not (BatSet.mem s existential_vars))
        in
        let new_pc = PolynomialCone.intersection current_pc projected_pc in
        let ideal = PolynomialCone.get_ideal new_pc in
        let ideal_generators = Polynomial.Ideal.generators ideal in
        let eq_zero_constraints = BatList.map
            (fun p -> mk_eq srk (mk_zero srk) (P.term_of srk term_of_int p))
            ideal_generators
        in
        let cone_generators = PolynomialCone.get_cone_generators new_pc in
        let geq_zero_constraints = BatList.map
            (fun p -> mk_leq srk (mk_zero srk) (P.term_of srk term_of_int p))
            cone_generators
        in
        let augmented_formula = mk_and srk
            [formula;
             (mk_not srk (mk_and srk (eq_zero_constraints @ geq_zero_constraints)))]
        in
        go new_pc augmented_formula
      end
      | `Unsat -> current_pc
      | `Unknown -> failwith "Cannot find a model for the current formula"
  in
  go pc phi




  

  


(* lazy consequence finding depends on this is_sat, and ideally we should build a solver interface
 * that supports checking if there is a model of the formula, and adding clauses to the formula. *)

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
module A = BatDynArray

module IntSet = SrkUtil.Int.Set

include Log.Make(struct let name = "srk.weaksolver" end)


let is_sat srk phi =
  (* Use normalize in quantifier.ml to get the existentials *)
  let phi = eliminate_ite srk phi in
  let phi =
    SrkSimplify.simplify_terms srk phi
  in
  let quantifiers, phi = Quantifier.normalize srk phi in
  (* This module should be sound wrt the theory, other things like x > 0 <=> x >= 1 happen in other modules *)
  (* cannot rewrite into negation normal form past equalities, since
     not (p = 0) is not equiv to p > 0 or p < 0
     since don't have total order *)
  assert (BatList.for_all (fun quant -> match quant with `Exists, _ -> true | _ -> false) quantifiers = true);
  (* let existentials = BatList.map (fun q -> match q with _, sym -> sym) quantifiers in *)
  let solver = Smt.mk_solver ~theory:"QF_LIRA" srk in
  let uninterp_phi =
    rewrite srk
      ~down:(nnf_rewriter srk)
      ~up:(Nonlinear.uninterpret_rewriter srk)
      phi
  in
  (* nonlinear is a map from symbols to term/formula *)
  let (lin_phi, nonlinear) = SrkSimplify.purify srk uninterp_phi in
  (* Creating a list of relationships between symbols and their meanings *)
  let nonlinear_defs =
    Symbol.Map.enum nonlinear
    /@ (fun (symbol, expr) ->
        match Expr.refine srk expr with
        | `Term t -> mk_eq srk (mk_const srk symbol) t
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
        let rec process_atoms l cs geqs eqs =
          match l with
          | [] -> (cs, geqs, eqs)
          | h :: t -> match (destruct srk h) with
              `Atom (`Eq, a, b) ->
              CS.admit_term cs a;
              CS.admit_term cs b;
              process_atoms t cs geqs ((mk_sub srk a b) :: eqs)
            | `Atom (`Leq, a, b) ->
              CS.admit_term cs a;
              CS.admit_term cs b;
              process_atoms t cs ((mk_sub srk b a) :: geqs) eqs
            | `Atom (`Lt, a, b) ->
              (* Handle disequations using polynomial cone membership *)
              CS.admit_term cs a;
              CS.admit_term cs b;
              process_atoms t cs ((mk_sub srk (mk_sub srk b (mk_one srk)) a) :: geqs) eqs
              | _ -> failwith "Encountered non-atom in the implicant selected."
        in
        let cs, geqs, eqs = process_atoms atoms (CS.mk_empty srk) [] [] in
        let geqs = BatList.map (fun expr -> CS.polynomial_of_term cs expr) geqs in
        let eqs = BatList.map (fun expr -> CS.polynomial_of_term cs expr) eqs in
        let initial_ideal = Polynomial.Ideal.make eqs in
        let pc = PolynomialCone.make_enclosing_cone initial_ideal geqs in
        if not (PolynomialCone.is_proper pc) then `Sat
        else
          begin
            Smt.Solver.add solver [(mk_not srk (mk_and srk atoms))]; go ()
          end
        (* Getting two lists of polynomial constraints Z, P *)
        (* call the procedure making_enclosing_cone to get the pair Z, P *)
        (* is_sat only needs to get one model, just see if the generated polynomial cone is non-proper *)

        (* if it is proper, then we get a model of this formula. If non-proper
         * add the blocking clause based on the list of atoms. Similar to how DPLL(T) works.
         * In the future, can try to get lemmas (find a subset of atoms whose conjunction is unsat)
         * preduce in the Grobner basis can be used to generate this.
         *
         *  *)

  in
  if Symbol.Map.is_empty nonlinear then
    Smt.Solver.check solver []
  else
    go ()

(* lazy consequence finding depends on this is_sat, and ideally we should build a solver interface
 * that supports checking if there is a model of the formula, and adding clauses to the formula. *)

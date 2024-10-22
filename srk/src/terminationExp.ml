open Syntax

include Log.Make(struct let name = "TerminationExp" end)
module TF = TransitionFormula
module IS = Iteration.Solver

let closure exp solver =
  let srk = IS.get_context solver in
  let qe = Syntax.mk_exists_consts srk in
  let k = mk_symbol srk `TyInt in
  let phi_k = (* approximate k-fold composition of phi *)
    exp solver (mk_const srk k)
  in 
  let f = mk_and srk [mk_leq srk (mk_zero srk) (mk_const srk k);
                      phi_k] in
  logf "Abstraction completed, k-fold formula: %a" (Formula.pp srk) f;
  qe (fun sym -> sym != k) f

let mp exp solver =
  let srk = Iteration.Solver.get_context solver in
  let qe = Syntax.mk_exists_consts srk in
  let k = mk_symbol srk `TyInt in
  let pre_to_post =
    List.fold_left (fun pre_to_post (x,x') ->
        Symbol.Map.add x (mk_const srk x') pre_to_post)
      Symbol.Map.empty
      (IS.get_symbols solver)
  in
  let tf = IS.get_formula solver in
  let phi_k = (* approximate k-fold composition of phi *)
    exp solver (mk_const srk k)
  in
  let pre_symbols =
    List.fold_left
      (fun set (s,_) -> Symbol.Set.add s set)
      (IS.get_constants solver)
      (IS.get_symbols solver)
  in
  let pre = qe (fun sym -> Symbol.Set.mem sym pre_symbols) tf in
  let pre' = (* pre'[x -> x', x' -> x''] *)
    substitute_map srk pre_to_post pre
  in
  let halt_within_k = (* pre-states for which computation must halt within k steps *)
    mk_and srk [phi_k; pre']
    |> qe (fun sym -> sym = k || (Symbol.Set.mem sym pre_symbols))
    |> mk_not srk
  in
  mk_and srk [mk_leq srk (mk_zero srk) (mk_const srk k);
              halt_within_k]
  |> qe (fun sym -> sym != k) (* express over pre-state symbols + symbolic constants *)

open Syntax

include Log.Make(struct let name = "TerminationExp" end)
module TF = TransitionFormula

let closure (module I : Iteration.PreDomain) srk tf =
  let qe = Syntax.mk_exists_consts srk in
  let k = mk_symbol srk `TyInt in
  let phi_k = (* approximate k-fold composition of phi *)
    I.abstract srk tf
    |> I.exp srk (TF.symbols tf) (mk_const srk k)
  in 
  let f = mk_and srk [mk_leq srk (mk_zero srk) (mk_const srk k);
                      phi_k] in
  logf "Abstraction completed, k-fold formula: %a" (Formula.pp srk) f;
  qe (fun sym -> sym != k) f

let mp (module I : Iteration.PreDomain) srk tf =
  let qe = Syntax.mk_exists_consts srk in
  let k = mk_symbol srk `TyInt in
  let (pre_to_post, post_sym) =
    List.fold_left (fun (pre_to_post, post_sym) (x,x') ->
        (Symbol.Map.add x (mk_const srk x') pre_to_post,
         Symbol.Set.add x' post_sym))
      (Symbol.Map.empty, Symbol.Set.empty)
      (TF.symbols tf)
  in
  let phi_k = (* approximate k-fold composition of phi *)
    I.abstract srk tf
    |> I.exp srk (TF.symbols tf) (mk_const srk k)
  in
  let pre =
    qe (fun sym -> TF.exists tf sym && not (Symbol.Set.mem sym post_sym)) (TF.formula tf)
  in
  let pre' = (* pre'[x -> x', x' -> x''] *)
    substitute_map srk pre_to_post pre
  in
  let halt_within_k = (* pre-states for which computation must halt within k steps *)
    mk_and srk [phi_k; pre']
    |> qe (fun sym -> sym = k || (TF.exists tf sym && not (Symbol.Set.mem sym post_sym)))
    |> mk_not srk
  in
  let result =
    mk_and srk [mk_leq srk (mk_zero srk) (mk_const srk k);
                halt_within_k]
    |> qe (fun sym -> sym != k) (* express over pre-state symbols + symbolic constants *)
  in
  result
(*
  match Quantifier.simsat srk result with
  | `Unsat -> mk_false srk
  | `Sat -> let f =  Syntax.mk_forall_consts srk (fun _ -> false) result in 
    begin
      match Quantifier.simsat srk f  with 
      | `Sat -> mk_true srk
      | _ -> result
    end
  | _ -> result
 *)

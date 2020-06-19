open Syntax

let mp (module I : Iteration.PreDomain) srk exists tr_symbols phi =
  let qe = Quantifier.mbp srk in
  let k = mk_symbol srk `TyInt in
  let phi_k = (* approximate k-fold composition of phi *)
    I.abstract ~exists srk tr_symbols phi
    |> I.exp srk tr_symbols (mk_const srk k)
  in
  let (pre_to_post, post_sym) =
    List.fold_left (fun (pre_to_post, post_sym) (x,x') ->
        (Symbol.Map.add x (mk_const srk x') pre_to_post,
         Symbol.Set.add x' post_sym))
      (Symbol.Map.empty, Symbol.Set.empty)
      tr_symbols
  in
  let phi' = (* phi[x -> x', x' -> x''] *)
    let rename_fresh =
      Memo.memo (fun sym ->
          mk_const srk (mk_symbol srk (typ_symbol srk sym)))
    in
    let subst sym =
      if Symbol.Map.mem sym pre_to_post then
        Symbol.Map.find sym pre_to_post
      else if exists sym && not (Symbol.Set.mem sym post_sym) then
        mk_const srk sym (* sym is a symbolic constant *)
      else
        rename_fresh sym (* sym is post symbol or Skolem constant *)
    in
    substitute_const srk subst phi
  in
  let halt_within_k = (* pre-states for which computation must halt within k steps *)
    mk_and srk [phi_k; phi']
    |> qe (fun sym -> sym = k || Symbol.Map.mem sym pre_to_post)
    |> mk_not srk
  in
  mk_and srk [mk_leq srk (mk_zero srk) (mk_const srk k); halt_within_k]
  |> qe (fun sym -> sym != k) (* express over pre-state symbols + symbolic constants *)

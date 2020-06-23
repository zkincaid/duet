open Syntax

include Log.Make(struct let name = "TerminationExp" end)


let closure (module I : Iteration.PreDomain) srk exists tr_symbols phi =
  let qe = Quantifier.mbp srk in
  let k = mk_symbol srk `TyInt in
  let phi_k = (* approximate k-fold composition of phi *)
    I.abstract ~exists srk tr_symbols phi
    |> I.exp srk tr_symbols (mk_const srk k)
  in 
  logf "abstraction completed";
  logf "k-fold formula: %s" (Formula.show srk phi_k);
  qe (fun sym -> sym != k) phi_k

let mp (module I : Iteration.PreDomain) srk exists tr_symbols phi =
  let qe = Quantifier.mbp srk in
  let k = mk_symbol srk `TyInt in

  let (pre_to_post, post_sym) =
    List.fold_left (fun (pre_to_post, post_sym) (x,x') ->
        (Symbol.Map.add x (mk_const srk x') pre_to_post,
         Symbol.Set.add x' post_sym))
      (Symbol.Map.empty, Symbol.Set.empty)
      tr_symbols
  in
  let phi_k = (* approximate k-fold composition of phi *)
    I.abstract ~exists srk tr_symbols phi
    |> I.exp srk tr_symbols (mk_const srk k)
  in
  let pre =
    qe (fun sym -> exists sym && not (Symbol.Set.mem sym post_sym)) phi
  in
  let pre' = (* pre'[x -> x', x' -> x''] *)
    substitute_map srk pre_to_post pre
  in
  let halt_within_k = (* pre-states for which computation must halt within k steps *)
    mk_and srk [phi_k; pre']
    |> qe (fun sym -> sym = k || (exists sym && not (Symbol.Set.mem sym post_sym)))
    |> mk_not srk
  in
  let result =
    mk_and srk [mk_leq srk (mk_zero srk) (mk_const srk k);
                halt_within_k]
    |> qe (fun sym -> sym != k) (* express over pre-state symbols + symbolic constants *)
  in
  mk_or srk [mk_not srk pre; result]

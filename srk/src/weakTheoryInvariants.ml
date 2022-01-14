open Syntax
open BatPervasives

module TF = TransitionFormula
module P = Polynomial
module PC = PolynomialCone
module WTS = WeakSolver
module CS = CoordinateSystem
module V = Linear.QQVector


include Log.Make(struct let name = "WeakTheoryInvariants" end)

let mem_cs cs x =
  try (ignore (CS.cs_term_id cs (`App (x,[]))); true)
  with Not_found -> false

let cs_of_symbols srk symbols =
  let cs = CS.mk_empty srk in
  List.iter (fun x -> CoordinateSystem.admit_cs_term cs (`App (x,[]))) symbols;
  cs

let filter_polys_linear_in_dims dims polys =
  let polys_linear_in_dx = BatList.filter_map
      (fun poly -> let lin, higher = P.QQXs.split_linear poly in
        let higher_contains_dx =
          BatEnum.exists
            (fun (_, mono) ->
               BatEnum.exists
                 (fun (dim, _) ->
                    if BatSet.Int.mem dim dims then
                      true
                    else false
                 )
                 (P.Monomial.enum mono)
            )
            (P.QQXs.enum higher)
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
      let other_linterm = V.sub lin linterm_of_only_dx in
      let other_poly = P.QQXs.of_vec other_linterm in
      if V.is_zero linterm_of_only_dx then None else Some (linterm_of_only_dx, P.QQXs.add other_poly higher)
    )
    polys_linear_in_dx


let find_inv_functionals dx_dims implied_ideal =
  logf "finding inv functionals";
  let basis = P.Rewrite.generators implied_ideal in
  filter_polys_linear_in_dims dx_dims basis

let find_tf_invs srk tr_symbols loop_counter tf =
  logf "finding transition formula invs";
  let x_xp = tr_symbols in
  (* For each variable x, create a symbol d_x representing x - x' *)
  let dx =
    List.map (fun (x, _) ->
        let name = String.concat "" ["d_"; show_symbol srk x] in
        mk_symbol srk ~name (typ_symbol srk x))
      x_xp
  in
  let dx_dims = BatList.fold_left (fun s dx ->
      logf "var %s dim %d" (show_symbol srk dx) (int_of_symbol dx);
      BatSet.Int.add (int_of_symbol dx) s)
      BatSet.Int.empty
      dx
  in
  (* let x_cs = cs_of_symbols srk (List.map fst x_xp) in *)
  let diff =
    List.map2 (fun (x,x') dx ->
        mk_eq srk (mk_const srk dx) (mk_sub srk (mk_const srk x) (mk_const srk x')))
      x_xp
      dx
  in
  let pp_dim = (fun formatter i ->
      try Format.fprintf formatter "%a" (pp_symbol srk) (symbol_of_int i)
      with _ -> Format.fprintf formatter "1")
  in
  let formula_with_dx = mk_and srk ((TF.formula tf) :: diff) in
  let consequence_cone = WTS.find_consequences srk formula_with_dx in
  logf "consequence cone is %a" (PC.pp pp_dim) consequence_cone;
  let implied_ideal = PC.get_ideal consequence_cone in
  let inv_functionals = find_inv_functionals dx_dims implied_ideal in
  BatList.iter (fun (inv, _) -> logf "Inv linear func: %a" V.pp inv) inv_functionals;
  let zs = BatList.mapi (fun i _ ->
      let name = String.concat "" ["z_"; string_of_int i] in
      mk_symbol srk ~name `TyReal)
      inv_functionals
  in
  let z_dims = BatList.fold (fun s z -> BatSet.Int.add (int_of_symbol z) s) BatSet.Int.empty zs in
  let inv_eqs = BatList.map2 (fun z (inv_func, _) ->
      mk_eq srk (mk_const srk z) (Linear.of_linterm srk inv_func)
    )
      zs
      inv_functionals
  in
  let formula_with_dx_inv = mk_and srk (formula_with_dx :: inv_eqs) in
  logf "formula with dx invs: %a" (Formula.pp srk) formula_with_dx_inv;
  let existential_formula = mk_exists_consts
      srk
      (fun symbol -> BatList.mem symbol dx || BatList.mem symbol zs)
      formula_with_dx_inv in
  let inv_cone = WTS.find_consequences srk existential_formula in
  logf "polynomial cone of delta and inv lin funcs: %a" (PC.pp pp_dim) inv_cone;
  logf "completed printing";
  let elim_z i = let sym = Syntax.symbol_of_int i in not (BatList.mem sym zs) in
  let elim_order = P.Monomial.block [not % elim_z] P.Monomial.degrevlex in
  let inv_cone_rewrite = PC.change_monomial_ordering inv_cone elim_order in
  logf "polynomial cone with elim ordering: %a" (PC.pp pp_dim) inv_cone_rewrite;
  let ideal = PC.get_ideal inv_cone_rewrite in
  let implied_zero_polys_of_inv_funcs =
    BatList.filter_map (fun p ->
        let is_poly_only_of_zs =
          BatEnum.for_all (fun (_, mono) ->
              BatEnum.for_all (fun (dim, _) ->
                  BatSet.Int.mem dim z_dims
                )
                (P.Monomial.enum mono)
            )
            (P.QQXs.enum p)
        in
        if is_poly_only_of_zs then Some p else None
      )
      (P.Rewrite.generators ideal)
  in
  let subst_zs_by_lin_comb_of_x = BatList.map (fun p ->
      P.QQXs.substitute (fun dim -> if BatSet.Int.mem dim z_dims then
                            let order_in_inv_func_list, _ = BatList.findi (fun _ sym -> int_of_symbol sym = dim) zs in
                            let inv_func, _ = BatList.nth inv_functionals order_in_inv_func_list in
                            P.QQXs.of_term srk (Linear.of_linterm srk inv_func)
                          else
                            P.QQXs.of_dim dim
                        )
        p
    )
  in
  let implied_zero_polys_in_x = subst_zs_by_lin_comb_of_x implied_zero_polys_of_inv_funcs in
  let term_of_poly p = P.QQXs.term_of srk (fun dim -> mk_const srk (symbol_of_int dim)) p in
  let implied_zero_polys_formulas = BatList.map (fun p -> mk_eq srk (mk_zero srk) (term_of_poly p)) implied_zero_polys_in_x in
  let nonnegs = PC.get_cone_generators inv_cone_rewrite in
  let lin_polys_in_dx_in_ideal = filter_polys_linear_in_dims dx_dims (P.Rewrite.generators ideal) in
  let lin_polys_in_dx_in_cone = filter_polys_linear_in_dims dx_dims nonnegs in
  let subst_dx_by_xp_minus_x = BatList.map (fun (v, poly) ->
      let term_of_v =
        Linear.term_of_vec srk (fun dim ->
            let order_in_dx_list, _ = BatList.findi (fun _ sym -> int_of_symbol sym = dim) dx in
            let x, xp = BatList.nth x_xp order_in_dx_list in
            (mk_sub srk (mk_const srk x) (mk_const srk xp))
          ) v
      in
      (term_of_v, poly)
    )
  in
  let implied_recurrent_poly_eqs = BatList.map (fun (lin_term_of_xp_minus_x, poly) ->
      mk_eq srk (mk_zero srk) (mk_sub srk lin_term_of_xp_minus_x (mk_mul srk [loop_counter; (term_of_poly poly)]))
    )
      (subst_dx_by_xp_minus_x lin_polys_in_dx_in_ideal)
  in
  let implied_recurrent_poly_ineqs = BatList.map (fun (lin_term_of_xp_minus_x, poly) ->
      mk_leq srk (mk_zero srk) (mk_sub srk lin_term_of_xp_minus_x (mk_mul srk [loop_counter; (term_of_poly poly)]))
    )
      (subst_dx_by_xp_minus_x lin_polys_in_dx_in_cone)
  in
  let trivial_transition_case = TF.formula (TF.identity srk tr_symbols) in
  let final_formula = mk_or srk [
      mk_and srk [
        mk_eq srk loop_counter (mk_real srk QQ.zero);
        trivial_transition_case
      ];
      mk_and srk [
        mk_leq srk (mk_real srk QQ.one) loop_counter;
        mk_and srk implied_recurrent_poly_eqs;
        mk_and srk implied_recurrent_poly_ineqs;
        mk_and srk implied_zero_polys_formulas
      ]
    ] in
  final_formula

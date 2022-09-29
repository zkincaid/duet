open Syntax
open BatPervasives

module TF = TransitionFormula
module P = Polynomial
module PC = PolynomialCone
module WTS = WeakSolver
module V = Linear.QQVector


include Log.Make(struct let name = "WeakTheoryInvariants" end)

let pp_dim srk = (fun formatter i ->
    try Format.fprintf formatter "%a" (pp_symbol srk) (symbol_of_int i)
    with _ -> Format.fprintf formatter "1")

(* Do all symbols in a polynomial satisfy the given predicate? *)
let for_all_vars predicate polynomial =
  BatEnum.for_all
    (fun (_, mono) ->
       BatEnum.for_all
         (fun (dim, _) -> predicate (symbol_of_int dim))
         (P.Monomial.enum mono))
    (P.QQXs.enum polynomial)

(* Find polynomials that can be written as the sum of a linear term over a
   designated set of variables and polynomial over the remaining variables. *)
let filter_polys_linear_in_dims predicate polys =
  BatList.filter_map
    (fun poly ->
       let lin, higher = P.QQXs.split_linear poly in
       if for_all_vars (not % predicate) higher then
         let (lin, higher) =
           BatEnum.fold
             (fun (lin, higher) (coeff, dim) ->
                if dim == Linear.const_dim then
                  (lin, P.QQXs.add_term coeff P.Monomial.one higher)
                else if predicate (symbol_of_int dim) then
                  (V.add_term coeff dim lin, higher)
                else
                  (lin, P.QQXs.add_term coeff (P.Monomial.singleton dim 1) higher))
             (V.zero, higher)
             (V.enum lin)
         in
         Some (lin, higher)
       else
         None)
    polys

let project_down_to_linear predicate pc =
  let order =
    P.Monomial.block [not % predicate % symbol_of_int] P.Monomial.degrevlex
  in
  let ideal =
    PolynomialCone.get_ideal pc
    |> P.Rewrite.reorder_groebner order
    |> P.Rewrite.restrict (fun m ->
        match P.Monomial.destruct_var m with
        | Some v -> predicate (symbol_of_int v)
        | None -> false)
  in
  PolynomialCone.make_cone ideal []

let find_inv_functionals dx_dims implied_ideal =
  let open Linear in
  let basis = P.Rewrite.generators implied_ideal in
  let polys = filter_polys_linear_in_dims dx_dims basis in
  let lin_part_mat =
    QQMatrix.transpose (QQMatrix.of_rows (BatList.map fst polys))
  in
  let const_parts =
    BatList.mapi
      (fun num ( _, const) -> (P.QQXs.coeff (P.Monomial.one) const, num))
      polys
  in
  let const_mat = QQMatrix.of_rows [QQVector.of_list const_parts] in
  let all_dims = BatList.of_enum (0 -- (BatList.length const_parts - 1)) in
  let null_space = nullspace const_mat all_dims in
  BatList.map
    (fun base_vec -> QQMatrix.vector_right_mul lin_part_mat base_vec)
    null_space

let compute_LIRR_invariants srk tr_symbols loop_counter tf =
  let tf = TF.map_formula (Nonlinear.eliminate_floor_mod_div srk) tf in
  (* For each variable x, create a symbol d_x representing x' - x *)
  let (dx_subst_diff, dx_subst_x, dx_defs) =
    List.fold_left
      (fun (dx_subst_diff, dx_subst_x, dx_defs) (x, x') ->
         let name = Format.asprintf "d_%a" (pp_symbol srk) x in
         let dx = mk_symbol srk ~name (typ_symbol srk x) in
         let diff = mk_sub srk (mk_const srk x') (mk_const srk x) in
         let dx_subst_diff = Symbol.Map.add dx diff dx_subst_diff in
         let dx_subst_x = Symbol.Map.add dx (mk_const srk x) dx_subst_x in
         let dx_defs = (mk_eq srk (mk_const srk dx) diff)::dx_defs in
         (dx_subst_diff, dx_subst_x, dx_defs))
      (Symbol.Map.empty, Symbol.Map.empty, [])
      tr_symbols
  in
  let formula_with_dx = mk_and srk ((TF.formula tf) :: dx_defs) in
  let is_dx x = Symbol.Map.mem x dx_subst_x in
  let inv_functionals =
    mk_exists_consts srk is_dx formula_with_dx
    |> WTS.abstract srk (project_down_to_linear is_dx)
    |> PC.get_ideal
    |> find_inv_functionals is_dx
    |> List.map (Linear.term_of_vec
                   srk
                   (fun i -> Symbol.Map.find (symbol_of_int i) dx_subst_x))
  in
  (* For each invariant functional f_i, create a symbol z_i representing f *)
  let (z_subst, z_defs) =
    BatList.fold_lefti
      (fun (z_subst, z_defs) i inv_func ->
         let name = Format.asprintf "z_%d" i in
         let z = mk_symbol srk ~name `TyReal in
         let z_subst = Symbol.Map.add z inv_func z_subst in
         let z_defs = (mk_eq srk (mk_const srk z) inv_func)::z_defs in
         (z_subst, z_defs))
      (Symbol.Map.empty, [])
      inv_functionals
  in
  let is_z x = Symbol.Map.mem x z_subst in
  let is_invariant_symbol x =
    is_z x || TF.is_symbolic_constant tf x
  in
  let existential_formula =
    mk_exists_consts
      srk
      (fun symbol -> is_invariant_symbol symbol || is_dx symbol)
      (mk_and srk (formula_with_dx :: z_defs))
  in
  (* dx variables may only appear linearly; *)
  let inv_cone =
    let elim_order = P.Monomial.block [is_dx % symbol_of_int] P.Monomial.degrevlex in
    let cl cone =
      PolynomialCone.change_monomial_ordering cone elim_order
      |> PC.restrict (fun m ->
          match P.Monomial.destruct_var m with
          | Some _ -> true
          | None -> BatEnum.for_all
                      (is_invariant_symbol % symbol_of_int % fst)
                      (P.Monomial.enum m))
    in
    WTS.abstract srk cl existential_formula
  in
  (* Convert polynomial to term, substituting z variables for corresponding
     invariant functionals *)
  let inv_term_of_poly =
    P.QQXs.term_of
      srk
      (fun dim ->
         let symbol = symbol_of_int dim in
         match Symbol.Map.find_opt symbol z_subst with
         | Some t -> t
         | None ->
           assert (TF.is_symbolic_constant tf symbol);
           mk_const srk symbol)
  in
  (* Convert term over dx variables to a term over the corresponding differences *)
  let diff_term_of_vec =
    Linear.term_of_vec
      srk
      (fun dim ->
         let symbol = symbol_of_int dim in
         match Symbol.Map.find_opt symbol dx_subst_diff with
         | Some t -> t
         | None -> mk_const srk symbol)
  in
  let zero = mk_zero srk in
  let ideal = PC.get_ideal inv_cone in
  let implied_zero_polys_formulas =
    BatList.filter_map (fun p ->
        if for_all_vars is_invariant_symbol p
        then Some (mk_eq srk zero (inv_term_of_poly p))
        else None)
      (P.Rewrite.generators ideal)
  in
  let implied_recurrent_poly_eqs =
    filter_polys_linear_in_dims is_dx (P.Rewrite.generators ideal)
    |> BatList.map (fun (vec, poly) ->
        mk_eq srk zero (mk_add srk [diff_term_of_vec vec
                                   ; mk_mul srk [loop_counter
                                                ; inv_term_of_poly poly]]))
  in
  let implied_recurrent_poly_ineqs =
    PC.get_cone_generators inv_cone
    |> filter_polys_linear_in_dims is_dx
    |> BatList.map (fun (vec, poly) ->
        mk_leq srk zero (mk_add srk [diff_term_of_vec vec
                                    ; mk_mul srk [loop_counter
                                                 ; inv_term_of_poly poly]]))
  in
  mk_or srk [
    mk_and srk [ (* Reflexive closure *)
      mk_eq srk loop_counter (mk_real srk QQ.zero);
      TF.formula (TF.identity srk tr_symbols)
    ];
    mk_and srk [
      mk_leq srk (mk_real srk QQ.one) loop_counter;
      mk_and srk implied_recurrent_poly_eqs;
      mk_and srk implied_recurrent_poly_ineqs;
      mk_and srk implied_zero_polys_formulas
    ]
  ]

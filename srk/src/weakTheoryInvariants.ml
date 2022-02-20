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

let pp_dim srk = (fun formatter i ->
      try Format.fprintf formatter "%a" (pp_symbol srk) (symbol_of_int i)
      with _ -> Format.fprintf formatter "1")

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

(*
x = x + 1
y = y - 1

generators (dx - 1), (dy + 1)
(dx + dy) in span(dx-1, dy+1)
x+y should be an inv functional

use homogenization as in the write-up to find all these
 *)
(* in consequence finding, can also throw out a lot of stuff, maybe worth
having an interface letting the user controlling what to throw out at
every step of consequence finding. Thus it can be used to
find linear consequences, affine/linear eqs, etc.
the idea also applies to the recurrence ineqs.
e.g. degree limitations, throwing out ineqs and keep only the eqs

set up the generators as columns of a matrix *)
(* let the generators be g1 ... gn

let c1 through cn be the constant parts of the generators

[ c1 ... cn ] x = 0
[ -1 1 ] x = 0
compute a basis for the solution and then
{ [ g1 ... gn ] b1 , ..., [ g1 ... gn ] bm }
 will be the basis for the space of inv functionals
 *)
(*
TODO: consider loop splitting in a monotone
F(x, x') /\ g(x) |= g(x')

or consider phase graph analysis as in the termaination analysis
for some fixed set of predicates
sign and direction preds makes sense
attractor region can also be used as a predicate (maybe not in this paper but next)


final comparison should be with cra and cra-split-loops



also need to check the monotonicity proof generalize to the inv gen case
also need to add the target node in addition to the source node
algebraic char of the star operator as well

*)

let find_inv_functionals dx_dims implied_ideal =
  logf "finding inv functionals";
  let open Linear in
  let basis = P.Rewrite.generators implied_ideal in
  let polys = filter_polys_linear_in_dims dx_dims basis in
  let lin_parts = BatList.map (fun (lin, _) -> lin) polys in
  let lin_part_mat = QQMatrix.transpose (QQMatrix.of_rows lin_parts) in
  logf "linear part matrix is: %a" QQMatrix.pp lin_part_mat;
  let const_parts = BatList.mapi (fun num ( _, const) -> (P.QQXs.coeff (P.Monomial.one) const, num)) polys in
  let const_vec = QQVector.of_list const_parts in
  let const_mat = QQMatrix.of_rows [const_vec] in
  logf "const part matrix is: %a" QQMatrix.pp const_mat;
  let all_dims = BatList.of_enum (0 -- (BatList.length const_parts - 1)) in
  let null_space = nullspace const_mat all_dims in
  let inv_bases = BatList.map (fun base_vec -> QQMatrix.vector_right_mul lin_part_mat base_vec) null_space in
  (* let const_bases = BatList.map (fun base_vec -> QQMatrix.vector_right_mul const_mat base_vec) null_space in *)
  inv_bases
  (* let polys = BatList.filter (fun (_, other) -> P.QQXs.equal P.QQXs.zero other) polys in *)



let find_tf_invs srk tr_symbols loop_counter tf =
  logf "finding transition formula invs for %a" (Formula.pp srk) (TF.formula tf) ;
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
        mk_eq srk (mk_const srk dx) (mk_sub srk (mk_const srk x') (mk_const srk x)))
      x_xp
      dx
  in
  let formula_with_dx = mk_and srk ((TF.formula tf) :: diff) in
  let formula_exists_dx = mk_exists_consts
      srk
      (fun symbol -> BatList.mem symbol dx)
      formula_with_dx in

  let consequence_cone = WTS.find_consequences srk formula_exists_dx in
  logf "consequence cone is %a" (PC.pp (pp_dim srk)) consequence_cone;
  let implied_ideal = PC.get_ideal consequence_cone in
  (* TODO: should also add symb constants as inv functionals *)
  let inv_functionals = find_inv_functionals dx_dims implied_ideal in
  let inv_functionals = BatList.map (fun f -> Linear.of_linterm srk f) inv_functionals in
  let sym_consts = Symbol.Set.to_list (TF.symbolic_constants tf) |> BatList.map (fun sym -> mk_const srk sym) in
  let inv_functionals = inv_functionals @ sym_consts in
  logf "printing inv functionals:";
  BatList.iter (fun inv -> logf "Inv func: %a" (ArithTerm.pp srk) inv) inv_functionals;
  logf "printing end";
  let zs = BatList.mapi (fun i _ ->
      let name = String.concat "" ["z_"; string_of_int i] in
      mk_symbol srk ~name `TyReal)
      inv_functionals
  in
  let z_dims = BatList.fold (fun s z -> BatSet.Int.add (int_of_symbol z) s) BatSet.Int.empty zs in
  let inv_eqs = BatList.map2 (fun z inv_func ->
      mk_eq srk (mk_const srk z)  inv_func
    )
      zs
      inv_functionals
  in
  let formula_with_dx_inv = mk_and srk (formula_with_dx :: inv_eqs) in
  logf "formula with dx defs: %a" (Formula.pp srk) formula_with_dx_inv;
  let existential_formula = mk_exists_consts
      srk
      (fun symbol -> TF.is_symbolic_constant tf symbol ||  BatList.mem symbol dx || BatList.mem symbol zs)
      formula_with_dx_inv in
  let inv_cone = WTS.find_consequences srk existential_formula in
  logf "polynomial cone of delta and inv lin funcs: %a" (PC.pp (pp_dim srk)) inv_cone;
  let elim_z i = let sym = Syntax.symbol_of_int i in not (BatList.mem sym zs) in
  let elim_order = P.Monomial.block [not % elim_z] P.Monomial.degrevlex in
  let inv_cone_rewrite = PC.change_monomial_ordering inv_cone elim_order in
  logf "polynomial cone with elim ordering: %a" (PC.pp (pp_dim srk)) inv_cone_rewrite;
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
  logf "implied_zero_polys_of_inv_funcs are:";
  BatList.iter (fun p -> logf "poly: %a" (P.QQXs.pp (pp_dim srk)) p) implied_zero_polys_of_inv_funcs;
  logf "printing end";
  let subst_zs_by_lin_comb_of_x = BatList.map (fun p ->
      P.QQXs.substitute (fun dim -> if BatSet.Int.mem dim z_dims then
                            let order_in_inv_func_list, _ = BatList.findi (fun _ sym -> int_of_symbol sym = dim) zs in
                            let inv_func = BatList.nth inv_functionals order_in_inv_func_list in
                            (* logf "linear.oflinterm is: %a" (ArithTerm.pp srk) (Linear.of_linterm srk inv_func); *)
                            P.QQXs.of_term srk inv_func
                          else
                            P.QQXs.of_dim dim
                        )
        p
    )
  in
  let implied_zero_polys_in_x = subst_zs_by_lin_comb_of_x implied_zero_polys_of_inv_funcs in
  logf "implied_zero_polys_in_x is:";
  BatList.iter (fun p -> logf "poly: %a" (P.QQXs.pp (pp_dim srk)) p) implied_zero_polys_in_x;
  logf "printing end";
  let term_of_poly p = P.QQXs.term_of srk (fun dim -> mk_const srk (symbol_of_int dim)) p in
  let implied_zero_polys_formulas = BatList.map (fun p -> mk_eq srk (mk_zero srk) (term_of_poly p)) implied_zero_polys_in_x in

logf "implied_zero_polys_formulas is:";
  BatList.iter (fun p -> logf "formula: %a" (Formula.pp srk) p) implied_zero_polys_formulas;
  let nonnegs = PC.get_cone_generators inv_cone_rewrite in
  let lin_polys_in_dx_in_ideal = filter_polys_linear_in_dims dx_dims (P.Rewrite.generators ideal) in
  logf "lin polys in dx in ideal";
  BatList.iter (fun (inv, other) -> logf "Inv linear func: %a, other part: %a" V.pp inv (P.QQXs.pp (pp_dim srk)) other) lin_polys_in_dx_in_ideal;
  let lin_polys_in_dx_in_cone = filter_polys_linear_in_dims dx_dims nonnegs in
  logf "lin polys in dx in cone";
  BatList.iter (fun (inv, other) -> logf "Inv linear func: %a, other part: %a" V.pp inv (P.QQXs.pp (pp_dim srk)) other) lin_polys_in_dx_in_cone;
  let subst_dx_by_xp_minus_x = BatList.map (fun (v, poly) ->
      let term_of_v =
        Linear.term_of_vec srk (fun dim ->
            let order_in_dx_list, _ = BatList.findi (fun _ sym -> int_of_symbol sym = dim) dx in
            let x, xp = BatList.nth x_xp order_in_dx_list in
            (mk_sub srk (mk_const srk xp) (mk_const srk x))
          ) v
      in
      (term_of_v, poly)
    )
  in
  let implied_recurrent_poly_eqs = BatList.map (fun (lin_term_of_xp_minus_x, poly) ->
      mk_eq srk (mk_zero srk) (mk_add srk [lin_term_of_xp_minus_x; (mk_mul srk [loop_counter; (term_of_poly poly)])])
    )
      (subst_dx_by_xp_minus_x lin_polys_in_dx_in_ideal)
  in
  logf "implied recurrent poly eqs is:";
  BatList.iter (fun f -> logf "eq: %a" (Formula.pp srk) f) implied_recurrent_poly_eqs;
  let implied_recurrent_poly_ineqs = BatList.map (fun (lin_term_of_xp_minus_x, poly) ->
      mk_leq srk (mk_zero srk) (mk_add srk [lin_term_of_xp_minus_x; (mk_mul srk [loop_counter; (term_of_poly poly)])])
    )
      (subst_dx_by_xp_minus_x lin_polys_in_dx_in_cone)
  in
  logf "implied recurrent poly ineqs is:";
  BatList.iter (fun f -> logf "eq: %a" (Formula.pp srk) f) implied_recurrent_poly_ineqs;
  let trivial_transition_case = TF.formula (TF.identity srk tr_symbols) in
  logf "trivial transition case is: %a" (Formula.pp srk) trivial_transition_case;
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
  logf "final formula is: %a" (Formula.pp srk) final_formula;
  final_formula

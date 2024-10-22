open Syntax
open BatPervasives

module TF = TransitionFormula
module P = Polynomial
module PC = PolynomialCone
module V = Linear.QQVector
module QQXs = P.QQXs

include Log.Make(struct let name = "LirrInvariants" end)

let pp_dim srk = (fun formatter i ->
    try Format.fprintf formatter "%a" (pp_symbol srk) (symbol_of_int i)
    with _ -> Format.fprintf formatter "1")

(* Do all symbols in a polynomial satisfy the given predicate? *)
let for_all_vars predicate polynomial =
  BatEnum.for_all
    (fun (_, mono) ->
       BatEnum.for_all
         (fun (dim, _) -> predicate dim)
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
                else if predicate dim then
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

let exp solver loop_counter =
  let srk = Iteration.Solver.get_context solver in
  let tr_symbols = Iteration.Solver.get_symbols solver in
  let pre_symbols =
    List.map (fun (s,_) -> mk_const srk s) tr_symbols
    |> Array.of_list
  in
  let delta =
    List.map
      (fun (s,s') -> mk_sub srk (mk_const srk s') (mk_const srk s))
      tr_symbols
    |> Array.of_list
  in
  let inv_functionals =
    Abstract.LinearSpan.abstract
      (Iteration.Solver.get_abstract_solver solver)
      delta
    |> List.map (Linear.term_of_vec srk (Array.get pre_symbols))
    |> Array.of_list
  in
  let delta_inv =
    Array.init ((Array.length delta) + (Array.length inv_functionals))
      (fun i ->
         if i < Array.length delta then
           delta.(i)
         else
           inv_functionals.(i - (Array.length delta)))
  in
  let is_delta i = i < Array.length delta in
  let delta_inv_polys = Array.map (QQXs.of_term srk) delta_inv in
  let elim_order = P.Monomial.block [is_delta] P.Monomial.degrevlex in
  let of_model = function
    | `LIRA _ -> assert false
    | `LIRR m ->
      (* Restrict to linear monomials over delta and monomials over the
         invariant functionals, which are associated with dimensions >= the
         length of delta *)
      let cone =
        PolynomialCone.inverse_image (Lirr.Model.nonnegative_cone m) delta_inv_polys
      in
      PolynomialCone.change_monomial_ordering cone elim_order
      |> PC.restrict (fun m ->
          match P.Monomial.destruct_var m with
          | Some _ -> true
          | None -> BatEnum.for_all
                      (fun (x, _) -> x >= Array.length delta)
                      (P.Monomial.enum m))
  in
  let formula_of = PC.to_formula srk (Array.get delta_inv) in
  let join =
    PC.intersection
  in
  let top = PC.top in
  let bottom = PC.make_cone (P.Rewrite.mk_rewrite P.Monomial.degrevlex [QQXs.one]) [] in
  let domain =
    Abstract.{ join; top; of_model; bottom; formula_of }
  in
  let rec_cone =
    Iteration.Solver.abstract solver domain
  in
  (* Convert vectors and polynomial to terms, associating dimension i to
     delta_inv[i] *)
  let term_of_qqxs = QQXs.term_of srk (Array.get delta_inv) in
  let term_of_vec = Linear.term_of_vec srk (Array.get delta_inv) in
  let zero = mk_zero srk in
  let implied_zero_polys_formulas =
    BatList.filter_map (fun p ->
        if for_all_vars (not % is_delta) p
        then Some (mk_eq srk zero (term_of_qqxs p))
        else None)
      (P.Rewrite.generators (PC.get_ideal rec_cone))
  in
  let implied_recurrent_poly_eqs =
    filter_polys_linear_in_dims is_delta (P.Rewrite.generators (PC.get_ideal rec_cone))
    |> BatList.map (fun (vec, poly) ->
        mk_eq srk zero (mk_add srk [term_of_vec vec
                                   ; mk_mul srk [loop_counter
                                                ; term_of_qqxs poly]]))
  in
  let implied_recurrent_poly_ineqs =
    PC.get_cone_generators rec_cone
    |> filter_polys_linear_in_dims is_delta
    |> BatList.map (fun (vec, poly) ->
        mk_leq srk zero (mk_add srk [term_of_vec vec
                                    ; mk_mul srk [loop_counter
                                                 ; term_of_qqxs poly]]))
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

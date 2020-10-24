open Syntax
open SolvablePolynomial

module Vec = Linear.QQVector
module Mat = Linear.QQMatrix
module TF = TransitionFormula

include Log.Make(struct let name = "TerminationDTA" end)

let pre_symbols tr_symbols =
  List.fold_left (fun set (s,_) ->
      Symbol.Set.add s set)
    Symbol.Set.empty
    tr_symbols

let post_symbols tr_symbols =
  List.fold_left (fun set (_,s') ->
      Symbol.Set.add s' set)
    Symbol.Set.empty
    tr_symbols

let simplify_condition srk condition_formula = 
  Quantifier.mbp ~dnf:true srk (fun _ -> true) condition_formula

(** Create symbols that stands for some linear terms and their defining
    equalities.
*)
let build_symbols_for_inv_terms srk inv_terms =
  let l_symbols, l_equalities, symbol_set = 
    BatArray.fold_righti
      (fun ind term (l_symbols, l_equalities, s) -> 
         let name_str = String.concat "_" ["dta"; "term"; (string_of_int ind)] in
         let symbol = mk_symbol srk ~name:name_str `TyReal in
         let const_expr = mk_const srk symbol in
         let equality = mk_eq srk term const_expr in
         (symbol :: l_symbols, equality :: l_equalities, Symbol.Set.add symbol s)
      )
      inv_terms
      ([], [], Symbol.Set.empty )
  in
  (l_symbols, l_equalities, symbol_set)

(** Transform a formula representation of a convex set f into a list of linear 
    inequalities. The linear inequalities are vectors where the meaning
    of the dimensions are given by the coordinate system cs.
*)
let get_polyhedron_of_formula srk srkf cs =
  let f = match Formula.destruct srk srkf with
    | `And xs -> xs
    | `Tru -> []
    | `Atom _ -> [ srkf ]
    | _ -> failwith "should not happen for convex polyhedra"
  in
  Polyhedron.of_implicant ~admit:true cs f
  |> Polyhedron.enum
  |> BatList.of_enum

(** Compute linear inequalities only involving the invariant symbols 
    entailed by the formula.
*)
let compute_linear_invariants srk formula inv_symbols_set =
  let polka = Polka.manager_alloc_strict () in
  let f = rewrite srk ~down:(nnf_rewriter srk) formula in
  let linear_invariants_apron =
    let exists x = Symbol.Set.mem x inv_symbols_set in
    Abstract.abstract ~exists:exists srk polka f
  in
  let linear_invariants = SrkApron.formula_of_property linear_invariants_apron in
  logf "\nInvariants on terms:\n%s\n\n" (Formula.show srk linear_invariants);
  linear_invariants

(** Compute the exponential polynomial that represents the transitive
    closure of a DLTS.
*)
let compute_exp_polynomial ?(square=false) best_dlts =
  let m =
    let module PLM = Lts.PartialLinearMap in
    let omega_domain = snd (PLM.iteration_sequence best_dlts.dlts) in
    PLM.map (PLM.make (PLM.map best_dlts.dlts) omega_domain)
  in
  let best_dlts_tr_matrix = if square then Linear.QQMatrix.mul m m else m in
  logf "getting squared is: %b" square;
  logf "matrix to be exponentiated: %a" (Linear.QQMatrix.pp) best_dlts_tr_matrix;
  let exp_poly_mat = if Linear.QQMatrix.zero == m then ExpPolynomial.Matrix.zero else
   match ExpPolynomial.exponentiate_rational best_dlts_tr_matrix with
    | None -> failwith "best rational DLTS abstraction produced a matrix with not all rational eigenvalues!"
    | Some mat -> mat
  in
  logf "Printing exp poly:\n%a\n" ExpPolynomial.Matrix.pp exp_poly_mat;
  exp_poly_mat

(** Get coefficient of a symbol within a linear term *)
let get_coeff_of_symbol cs vec symbol =
  let tid = CoordinateSystem.cs_term_id cs (`App (symbol, [])) in
  let c = Vec.coeff tid vec in
  c

(** For a linear term, get its vector representation w.r.t. a list of symbols. 
    For example, x + 2z + 1 w.r.t. [x, y, z] is represented by a tuple 
    containing a vector and the constant term:
      ([1, 0, 2], 1)
*)
let get_coeff_vec_for_expression cs expression list_symbols = 
  let vec = 
    BatList.fold_lefti
      (fun existing_coeffs i symbol -> 
         try
           let coeff = get_coeff_of_symbol cs expression symbol in
           Vec.add_term coeff i existing_coeffs 
         with Not_found -> Vec.add_term QQ.zero i existing_coeffs 
      )
      Vec.zero
      list_symbols
  in
  let const = Vec.coeff CoordinateSystem.const_id expression in
  (vec, const)


type ineq_type = Lt0 | Eq0 | Leq0

(** This data structure is a map with key type (QQ.t, int) and value type QQVector.
    Ordering on the keys is the lexicographic ordering, and value types
    form an Abelian group.
    This is used to store a term in an exponential polynomial. 
    For example, a term could look like 2^k * (k^3) * (2x + y + z) where
    k is the symbolic loop counter, and x, y, z are the initial values of
    variables x, y, z.
*)
module BaseDegPairMap = struct
  type pair = QQ.t * int [@@deriving ord]
  module QQV = Linear.QQVector
  module E = SparseMap.Make(struct type t = pair [@@deriving ord] end)(QQV)

  type t = E.t

  let empty = E.zero

  (** Put a term into the data structure. 
      index_pair: the base and the degree of the symbolic loop counter.
      factor: a multiplicative factor.
      non_zero_dim: an int that correspond to a particular dimension, and
          -1 correspond to constants
      p: the Abelian group map
  *)
  let put index_pair factor non_zero_dim p =
    let qqxvec = QQV.of_list [factor, non_zero_dim] in
    E.set index_pair (QQV.add (E.get index_pair p) qqxvec) p


  let has_higher_order_than_const base deg =
    (QQ.lt (QQ.of_int 1) base) || (( QQ.equal (QQ.of_int 1) base ) && deg >= 1)

  let has_lower_order_than_const base =
    (QQ.lt base (QQ.of_int 1) )

  let has_const_order base deg =
    QQ.equal QQ.one base && deg == 0

  (** Rank the items in the data structure according to dominance ordering and
      produce a formula for sufficient condition for termination.
      p: the Abelian group map.
      invariant_terms: these are the linear terms whose closed forms are computed
          during the symbolic exponentiation of transition matrix. This is 
          used to interpret the meaning of the vectors as values in the map.
      lhs_const: the constant that appears in the closed form formula.
      ineq_type: whether this inequality is <=, = or <.
  *)
  let rank srk p invariant_terms lhs_const ineq_type =
    logf "entering rank";
    let e = E.enum p in
    let dim_to_term = fun d -> if d < 0 then mk_one srk else BatList.nth invariant_terms d in
    let dom_ranked_list = 
      BatEnum.fold
        (fun l ((base, deg), qqt) -> 
           logf "base:%a deg:%d vec:%a\n"
             QQ.pp base 
             deg 
             QQV.pp qqt;
           (base, deg, qqt) :: l
        ) 
        []
        e
    in
    let conditions = 
      logf "start printing conditions list and formula stems";
      let conditions_list_final, formula_stem_list, encountered_const_order = 
        BatList.fold_left
          (fun (conditions_list, formula_stem, flag) (base, deg, qqt)  ->
             if has_const_order base deg then
               (** where the coefficient for const order term is non-zero
                   combine the term with the constant to derive a condition *)
               begin
                 logf "constant order base case";
                 let condition_lhs = Linear.term_of_vec srk dim_to_term qqt in
                 let lhs = mk_add srk [mk_real srk QQ.zero ; condition_lhs] in
                 let lhs_lt_zero = mk_lt srk lhs (mk_zero srk) in
                 let lhs_eq_zero = mk_eq srk lhs (mk_zero srk) in
                 let current_condition = mk_and srk (lhs_lt_zero :: formula_stem) in
                 let updated_stem = lhs_eq_zero :: formula_stem in
                 logf "lhs_lt_zero is: %a" (Formula.pp srk) lhs_lt_zero;
                 logf "lhs_eq_zero is: %a" (Formula.pp srk) lhs_eq_zero;
                 logf "current_condition is: %a" (Formula.pp srk) current_condition;
                 (current_condition :: conditions_list, updated_stem, true)           
               end
             else 
             if has_lower_order_than_const base then
               (** if we have no control over the const order, then doing
                   analysis on terms dominated by the const does not make sense *)
               if flag || QQ.equal QQ.zero lhs_const then
                 (** if we can control the const order *)
                 begin 
                   logf "lower order than constant order base case but has terms dominating the const";
                   let condition_lhs = Linear.term_of_vec srk dim_to_term qqt in
                   let lhs_lt_zero = mk_lt srk condition_lhs (mk_zero srk) in
                   let lhs_eq_zero = mk_eq srk condition_lhs (mk_zero srk) in
                   let current_condition = mk_and srk (lhs_lt_zero :: formula_stem) in
                   let updated_stem = lhs_eq_zero :: formula_stem in
                   logf "lhs_lt_zero is: %a" (Formula.pp srk) lhs_lt_zero;
                   logf "lhs_eq_zero is: %a" (Formula.pp srk) lhs_eq_zero;
                   logf "current_condition is: %a" (Formula.pp srk) current_condition;
                   (current_condition :: conditions_list, updated_stem, flag)
                 end
               else
                 (conditions_list, formula_stem, flag)
             else
               (** ordinary dominant term analysis for terms that dominate constant*)
               begin
                 logf "constant order base case";
                 let condition_lhs = Linear.term_of_vec srk dim_to_term qqt in
                 let lhs_lt_zero = mk_lt srk condition_lhs (mk_zero srk) in
                 let lhs_eq_zero = mk_eq srk condition_lhs (mk_zero srk) in
                 let current_condition = mk_and srk (lhs_lt_zero :: formula_stem) in
                 let updated_stem = lhs_eq_zero :: formula_stem in
                 logf "lhs_lt_zero is: %a" (Formula.pp srk) lhs_lt_zero;
                 logf "lhs_eq_zero is: %a" (Formula.pp srk) lhs_eq_zero;
                 logf "current_condition is: %a" (Formula.pp srk) current_condition;
                 (current_condition :: conditions_list, updated_stem, flag)
                 (** the term being considered is dominated by constant *)
               end
          )
          ([], [], false)
          dom_ranked_list
      in
      match ineq_type with
      | Lt0  -> 
        mk_not srk (mk_or srk conditions_list_final)
      | Eq0 -> 
        begin
          if BatList.is_empty conditions_list_final then
            (** we have started with a dominanting constant out of our control,
                behavior is captured by the constant on LHS *)          
            if QQ.equal QQ.zero lhs_const then 
              (** if const on LHS is 0, at far away the LHS is 0 *)
              mk_false srk
            else 
              (** if const on LHS is nonzero, the invariant will not hold 
                  for large enough no. of iterations *)
              mk_true srk
          else if encountered_const_order then
            (** have control over the constants, build everything as usual *)
            mk_not srk (mk_and srk formula_stem_list)
          else
            (** no control over the constant *)
          if QQ.equal lhs_const QQ.zero then
            (** but the constant itself alone is 0, 
                let all coefficients be 0 is fine here*)
            mk_not srk (mk_and srk formula_stem_list)
          else 
            (** cannot remain 0 forever, has to terminate *)
            mk_true srk
        end
      | Leq0 ->         
        mk_not srk (mk_or srk ( (mk_and srk formula_stem_list) :: conditions_list_final)) 
    in
    conditions
end

(** We obtained the termination condition in terms of some linear terms.
    Now we want to rewrite it into a form that only contains program variables.
    simulation: the linear terms in the DLTS abstraction
    invariant_symbols: aux symbols that we have defined for these terms
    formula: the conditions to be rewritten
*)
let rewrite_term_condition srk simulation invariant_symbols formula =
  let m = BatList.fold_lefti
      (fun m i inv_symb -> 
         Symbol.Map.add inv_symb (BatArray.get simulation i) m
      )
      Symbol.Map.empty
      invariant_symbols
  in
  substitute_map srk m formula

(** The main function for generating terminating conditions. 
    cs: coordinate system.
    lhs: the invariant inequalities' LHS.
    exp_poly: the closed form of the transitive closure.
    invariant_symbols: aux symbols we have defined for the linear terms appears
        in the DLTS abstraction process.
    invariant_terms: list of linear terms appears in DLTS abstraction.
    ineq_type: is the invariant inequality <, <= or =.
    best_DLTS_abstraction: the best DLTS abstraction of the transition formula
*)
let generate_term_cond srk cs lhs exp_poly invariant_symbols invariant_terms ineq_type best_DLTS_abstraction =
  let lt_vec, lhs_const = get_coeff_vec_for_expression cs lhs invariant_symbols in
  logf "\nlt_vec is: %a, LHS constant is: %a" 
    Vec.pp lt_vec 
    QQ.pp lhs_const;
  let lt_vec_exppoly = ExpPolynomial.Vector.of_qqvector lt_vec in
  let closed_form_vec = ExpPolynomial.Matrix.vector_left_mul lt_vec_exppoly exp_poly in
  let mat = ExpPolynomial.Matrix.of_rows [closed_form_vec] in
  logf "\nfinal matrix is: %a, with %d rows and %d cols" ExpPolynomial.Matrix.pp mat (ExpPolynomial.Matrix.nb_rows mat) (ExpPolynomial.Matrix.nb_columns mat);
  let mat_entries = ExpPolynomial.Matrix.entries mat in
  let has_negative_base = BatEnum.exists 
      (fun (_, _, entry) -> 
         begin
           logf "looking into entry %a for negative eigenvalues" ExpPolynomial.pp entry;
           let exppoly_terms_enum = ExpPolynomial.enum entry in
           BatEnum.exists 
             (fun (poly, base) -> 
                logf "this entry has polynomial %a and base %a" Polynomial.QQX.pp poly QQ.pp base; 
                QQ.lt base QQ.zero)
             exppoly_terms_enum
         end
      )
      mat_entries
  in
  let analyze_entries entries =
    begin
      logf "start iterating entries";
      let m = BaseDegPairMap.put (QQ.one, 0) lhs_const (-1) BaseDegPairMap.empty in
      let m = BatEnum.fold 
          ( fun m (idx, idy, entry) ->
              if idx != 0 then failwith "got a matrix with more than 1 row"
              else
                logf "iterating this entry: %a at x: %d, y: %d" ExpPolynomial.pp entry idx idy;
              let exppoly_terms_enum = ExpPolynomial.enum entry in
              BatEnum.fold
                (fun m (poly, base) -> 
                   let poly_terms_enum = Polynomial.QQX.enum poly in
                   BatEnum.fold
                     (fun m (coeff, deg) -> 
                        let index_pair = (base, deg) in
                        logf "putting into map: base: %a, deg: %d, coeff: %a" 
                          QQ.pp base
                          deg
                          QQ.pp coeff;
                        BaseDegPairMap.put index_pair coeff idy m
                     )
                     m
                     poly_terms_enum
                )
                m
                exppoly_terms_enum
          )
          m
          entries
      in
      let conditions = BaseDegPairMap.rank srk m invariant_terms lhs_const ineq_type in
      logf "terminating condition: %a" (Formula.pp srk) conditions;
      conditions
    end
  in

  if has_negative_base then
    begin
      logf "has negative eigenvalues, do alternative computation";
      let exppoly2 = compute_exp_polynomial ~square:true best_DLTS_abstraction in
      let closed_form_vec = ExpPolynomial.Matrix.vector_left_mul lt_vec_exppoly exppoly2 in
      let mat2 = ExpPolynomial.Matrix.of_rows [closed_form_vec] in
      logf "\nfinal matrix in this case is: %a" ExpPolynomial.Matrix.pp mat2;
      let entries = ExpPolynomial.Matrix.entries mat2 in
      let sat_even_conditions' = analyze_entries entries in
      let sat_even_conditions'' = rewrite_term_condition srk best_DLTS_abstraction.simulation invariant_symbols sat_even_conditions' in
      let sat_even_conditions = sat_even_conditions'' in
      logf "start computing sat_odd conditions";
      let entries = ExpPolynomial.Matrix.entries mat in
      let entries_with_odd_exp = BatEnum.map (
          fun (x, y, entry) -> 
            let t = ExpPolynomial.compose_left_affine entry 2 1 in
            logf "old entry at (%d, %d) is: %a" x y ExpPolynomial.pp entry;
            logf "new entry at (%d, %d) is: %a" x y ExpPolynomial.pp t;
            (x, y, t)
        ) 
          entries 
      in
      let sat_odd_conditions = analyze_entries entries_with_odd_exp in
      logf "sat_odd conditions: %a" (Formula.pp srk) sat_odd_conditions; 
      let results = Syntax.mk_or srk [sat_even_conditions; sat_odd_conditions] in
      logf "terminating conditions for this mat with neg spectrum: %a" (Formula.pp srk) results;
      results
    end
  else
    begin
      let mat_entries = ExpPolynomial.Matrix.entries mat in
      analyze_entries mat_entries
    end

(** Analyze the convex polyhedron entailed by the transition formula, get the invariant
    inequalities, and extract sufficient terminating conditions by looking at these
    inequalities.
    cs: coordinate system.
    invariants_polyhedron: the convex polyhedron entailed by the transition formula.
    exp_poly: the closed form of the transitive closure.
    invariant_symbols: aux symbols we have defined for the linear terms appears
        in the DLTS abstraction process.
    invariant_terms: list of linear terms appears in DLTS abstraction.
    best_DLTS_abstraction: the best DLTS abstraction of the transition formula
*)
let analyze_inv_polyhedron srk cs invariants_polyhedron exp_poly invariant_symbols invariant_terms best_DLTS_abstraction =
  let conditions_list = 
    BatList.fold_left
      (fun conditions eq -> 
         let ineqt, lhs = match eq with
           | `LtZero t -> Lt0, t
           | `EqZero t -> Eq0, t
           | `LeqZero t -> Leq0, t
         in 
         let cond = generate_term_cond srk cs lhs exp_poly invariant_symbols invariant_terms ineqt best_DLTS_abstraction in
         logf "terminating conditions for this ineq: %a" (Formula.pp srk) cond;
         cond :: conditions 
      )
      []
      invariants_polyhedron
  in
  mk_or srk conditions_list

(** Provide the swf operator using the dominant term analysis. *)
let compute_swf_via_DTA srk tf =
  let tf = TF.linearize srk tf in
  match Smt.is_sat srk (TF.formula tf) with
  | `Sat ->
    let best_DLTS_abstraction = DLTSPeriodicRational.abstract_rational srk tf in
    let invariant_symbols, inv_equalities, invariant_symbol_set =
      build_symbols_for_inv_terms srk best_DLTS_abstraction.simulation
    in
    let invariant_terms = BatList.map (fun symbol -> mk_const srk symbol) invariant_symbols in
    let formula = mk_and srk [TF.formula tf; mk_and srk inv_equalities] in
    logf "\nTransition formula with inv_terms:\n%s\n\n" (Formula.show srk formula);
    let linear_invariants = compute_linear_invariants srk formula invariant_symbol_set in
    let cs = CoordinateSystem.mk_empty srk in
    let invariants_polyhedron = get_polyhedron_of_formula srk linear_invariants cs in
    logf "\nPrinting invariants polyhedron:\n";
    let () = BatList.iter (function
        | `LeqZero t -> logf "%a <= 0" (CoordinateSystem.pp_vector cs) t
        | `LtZero t -> logf "%a < 0" (CoordinateSystem.pp_vector cs) t
        | `EqZero t -> logf "%a = 0" (CoordinateSystem.pp_vector cs) t) invariants_polyhedron
    in
    let exp_poly = compute_exp_polynomial best_DLTS_abstraction in
    let results_in_inv_terms = analyze_inv_polyhedron srk cs invariants_polyhedron exp_poly invariant_symbols invariant_terms best_DLTS_abstraction in
    logf "terminating conditions in inv terms: %a" (Formula.pp srk) results_in_inv_terms;
    let results = rewrite_term_condition srk best_DLTS_abstraction.simulation invariant_symbols results_in_inv_terms in
    logf "terminating conditions: %a" (Formula.pp srk) results;
    mk_not srk results
  | `Unknown -> failwith "SMT solver should not return unknown for QRA formulas"
  | `Unsat -> (logf ~attributes:[`Bold; `Green] "Transition formula UNSAT, done"); mk_false srk

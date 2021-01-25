open Syntax
open SolvablePolynomial
open BatPervasives


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
         let symbol =
           mk_symbol srk ~name:name_str (expr_typ srk term)
         in
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

let compute_rep_matrix best_dlts = 
  let module PLM = Lts.PartialLinearMap in
  let omega_domain = snd (PLM.iteration_sequence best_dlts.dlts) in
  let rep = PLM.map (PLM.make (PLM.map best_dlts.dlts) omega_domain) in
  rep


(** Compute the exponential polynomial that represents the transitive
    closure of a DLTS.
*)
let compute_exp_polynomial ?(square=false) m =
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
                 let lhs = mk_add srk [mk_zero srk; condition_lhs] in
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
                 logf "bigger than constant order base case";
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
          logf "inequation type is = 0";
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
            begin
            logf "have encountered constant order terms";
            mk_not srk (mk_and srk formula_stem_list)
            end
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
      let m = compute_rep_matrix best_DLTS_abstraction in
      let exppoly2 = compute_exp_polynomial ~square:true m in
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

  let compose_simulation srk mS simulation =
    Linear.QQMatrix.rowsi mS
    /@ (fun (_, row) ->
      Linear.term_of_vec srk (fun i -> simulation.(i)) row
      |> SrkSimplify.simplify_term srk)
    |> BatArray.of_enum

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
    let m = compute_rep_matrix best_DLTS_abstraction in
    let sim = best_DLTS_abstraction.simulation in
    let module PLM = Lts.PartialLinearMap in
    let omega_domain = snd (PLM.iteration_sequence best_DLTS_abstraction.dlts) in
    let omega_dom_mat = Linear.QQMatrix.of_rows omega_domain in
    let constraints_lhs = compose_simulation srk omega_dom_mat sim in
    let constraints = BatArray.fold_left (fun f term -> mk_and srk [f; mk_eq srk (mk_zero srk) term]) (mk_true srk) constraints_lhs in
    let exp_poly = compute_exp_polynomial m in
    let results_in_inv_terms = analyze_inv_polyhedron srk cs invariants_polyhedron exp_poly invariant_symbols invariant_terms best_DLTS_abstraction in
    logf "terminating conditions in inv terms: %a" (Formula.pp srk) results_in_inv_terms;
    let results = rewrite_term_condition srk best_DLTS_abstraction.simulation invariant_symbols results_in_inv_terms in
    logf "terminating conditions: %a" (Formula.pp srk) results;
    mk_and srk [mk_not srk results; constraints]
  | `Unknown -> failwith "SMT solver should not return unknown for QRA formulas"
  | `Unsat -> (logf ~attributes:[`Bold; `Green] "Transition formula UNSAT, done"); mk_false srk

module XSeq = struct 
  type t 
  type 'a seq_type = ('a Formula.t) BatDynArray.t

  let seq_op op x y =
    logf "entering seq_op";
    let x_len = BatDynArray.length x in 
    let y_len = BatDynArray.length y in 
    let common_len = match ZZ.to_int (ZZ.lcm (ZZ.of_int x_len) (ZZ.of_int y_len)) with 
    | None -> failwith "cannot compute lcm"
    | Some l -> l 
    in
    logf "lcm of both lengths is: %d" common_len;
    let result = BatDynArray.make common_len in 
    for i = 0 to common_len-1 do 
      BatDynArray.add 
      result 
      (op 
        (BatDynArray.get x (i mod x_len)) 
        (BatDynArray.get y (i mod y_len)))
    done;
    result

  let seq_of_true srk =
    BatDynArray.of_list [mk_true srk]

  let seq_of_false srk =
    BatDynArray.of_list [mk_false srk]
    
  let seq_and srk x y = 
    seq_op (fun a b -> mk_and srk [a; b]) x y 

  let seq_and srk xs =
    BatList.fold_left (fun s x -> seq_and srk s x) (seq_of_true srk) xs
  
  let seq_or srk x y =
    seq_op (fun a b -> mk_or srk [a; b]) x y

  let seq_or srk xs =
    BatList.fold_left (fun s x -> seq_or srk s x) (seq_of_false srk) xs

  let seq_add srk x y =
    seq_op (fun a b -> mk_add srk [a; b]) x y

  let seq_mul_symbol srk x symbol =
    BatDynArray.map (fun f -> mk_mul srk [f; mk_const srk symbol]) x

  let seq_not srk x = 
    BatDynArray.map (fun f -> mk_not srk f) x

  let seq_eq_zero srk x = 
    BatDynArray.map (fun f -> mk_eq srk f (mk_zero srk)) x

  let seq_conditions srk x =
    mk_not srk (mk_and srk (BatDynArray.to_list x))

  let seq_of_exp modulus lambda =
    (* Find period & start of the ultimately periodic sequence *)
    let rec detect_cycle i current seen =
      if BatMap.Int.mem current seen then
        let period = i - (BatMap.Int.find current seen) in
        (* Multiple of period between previous & current occurrence *)
        let start_pos = i - (i mod period) in
        (start_pos, period)
      else
        let next = (lambda * current) mod modulus in
        detect_cycle (i + 1) next (BatMap.Int.add current i seen)
    in
    let (start_pos, period) = detect_cycle 0 (1 mod modulus) BatMap.Int.empty in
    let start = (* lambda^start_pos *)
      SrkUtil.exp (fun x y -> (x * y) mod modulus) 1 lambda start_pos
    in
    let rec construct_seq current len seq =
      if len == 0 then
        List.rev seq
      else
        construct_seq
          ((lambda * current) mod modulus)
          (len - 1)
          (current::seq)
    in
    BatDynArray.of_list (construct_seq start period [])

    let seq_of_polynomial srk modulo poly =    
      let seq = BatDynArray.create () in 
      for i = 0 to (modulo - 1) do
        let p_at_i = Polynomial.QQX.term_of srk (mk_int srk i) poly in
        let p_at_i_mod = mk_mod srk p_at_i (mk_int srk modulo) in
        BatDynArray.add seq p_at_i_mod;
      done;
      seq

    let seq_of_single_base_exp_polynomial srk modulo poly base =
      let seq_of_exp = seq_of_exp modulo base in
      let seq_of_poly = seq_of_polynomial srk modulo poly in
      seq_op 
        (fun n term -> 
            mk_mod 
              srk 
              (mk_mul srk [ (mk_int srk n); term]) 
              (mk_int srk modulo)
        ) 
      seq_of_exp
      seq_of_poly

      let seq_of_exp_polynomial srk modulo exppoly =
        let e = ExpPolynomial.enum exppoly in 
        BatEnum.fold 
          (fun existing_seq (poly, base) -> 
            let b = match QQ.to_int base with 
              Some i -> i 
              | None -> failwith "Did not expect non-integer bases here"
            in
            let current_seq = seq_of_single_base_exp_polynomial srk modulo poly b in 
            if (BatDynArray.empty existing_seq) then current_seq else
              seq_add srk existing_seq current_seq
          )
        (BatDynArray.of_list [])
        e 
            

    (** For a linear term, get its vector representation w.r.t. a list of symbols. 
    For example, x + 2z + 1 w.r.t. [x, y, z] is represented by a tuple 
    containing a vector and the constant term:
      ([1, 0, 2], 1)
    *)
    let get_coeff_vec_wrt_symbol_list expression list_symbols = 
      let vec = 
        BatList.fold_lefti
          (fun existing_coeffs i symbol -> 
            try
              let coeff = Vec.coeff (Linear.dim_of_sym symbol) expression in
              Vec.add_term coeff i existing_coeffs 
            with Not_found -> Vec.add_term QQ.zero i existing_coeffs 
          )
          Vec.zero
          list_symbols
      in
      let const = Vec.coeff CoordinateSystem.const_id expression in
      (vec, const)


    let generate_xseq srk lhs ineq_type exp_poly abstraction = 
      let (invariant_symbols, invariant_terms, best_DLTS_abstraction) = abstraction in
      let lt_vec, lhs_const = get_coeff_vec_wrt_symbol_list lhs invariant_symbols in
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
          let conditions = mk_not srk (BaseDegPairMap.rank srk m invariant_terms lhs_const ineq_type) in
          logf "terminating condition: %a" (Formula.pp srk) conditions;
          conditions
        end
      in

      if has_negative_base then
        begin
          logf "has negative eigenvalues, do alternative computation";
          let m = compute_rep_matrix best_DLTS_abstraction in
          let exppoly2 = compute_exp_polynomial ~square:true m in
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
          let results = BatDynArray.of_list [sat_even_conditions; sat_odd_conditions] in
          results
        end
      else
        begin
          let mat_entries = ExpPolynomial.Matrix.entries mat in
          let res = analyze_entries mat_entries in 
          BatDynArray.of_list [res]
        end

    
    let seq_of_compare_zero_atom srk op vec exp_poly abstraction =
      let ineq_type, lhs_vec = match op with
           | `Lt -> Lt0, vec
           | `Eq -> Eq0, vec
           | `Leq -> Leq0, vec
         in 
      generate_xseq srk lhs_vec ineq_type exp_poly abstraction

    let seq_of_divides_atom srk zz_divisor dividend_vec exp_poly abstraction =
      let divisor = match ZZ.to_int zz_divisor with
      Some i -> i | None -> failwith "see non-integer divisor, error"
      in
      let (invariant_symbols, _, _) = abstraction in
      let lt_vec, lhs_const = get_coeff_vec_wrt_symbol_list dividend_vec invariant_symbols in
      logf "\nlt_vec is: %a, LHS constant is: %a" 
        Vec.pp lt_vec 
        QQ.pp lhs_const;
      let lt_vec_exppoly = ExpPolynomial.Vector.of_qqvector lt_vec in
      let closed_form_dividend = ExpPolynomial.Matrix.vector_left_mul lt_vec_exppoly exp_poly in
      let dividend_enum = ExpPolynomial.Vector.enum closed_form_dividend in 
      let dividend_xseqs = BatEnum.fold 
        (fun existing_seq (exppoly, dim) -> 
          let current_seq = seq_mul_symbol srk (seq_of_exp_polynomial srk divisor exppoly) (List.nth invariant_symbols dim) in 
          if BatDynArray.empty existing_seq then current_seq else 
            seq_add srk existing_seq current_seq
        )
        (BatDynArray.of_list [])
        dividend_enum
      in
      let mk_divides t =
        mk_eq srk (mk_mod srk t (mk_real srk (QQ.of_int divisor))) (mk_zero srk)
      in
      BatDynArray.map mk_divides dividend_xseqs

    let seq_of_notdivides_atom srk zz_divisor dividend_vec exp_poly abstraction =
      seq_of_divides_atom srk zz_divisor dividend_vec exp_poly abstraction
      |> seq_not srk

  let scaling_simulation srk best_DLTS_abstraction = 
    let sim = best_DLTS_abstraction.simulation in 
    let lcm_of_denominators = BatArray.fold_left (fun d term -> 
      let coeff_vec = Linear.linterm_of srk term in
      let e = Linear.QQVector.enum coeff_vec in 
      let t = BatEnum.fold (fun dd (coeff, _) -> let z = QQ.denominator coeff in ZZ.lcm dd z) ZZ.one e in 
      ZZ.lcm d t
     ) ZZ.one sim in
    let new_sim = BatArray.map (fun orig_term -> 
      let coeff_vec = Linear.linterm_of srk orig_term in 
      let new_vec = Linear.QQVector.scalar_mul (QQ.of_zz lcm_of_denominators) coeff_vec in 
      Linear.of_linterm srk new_vec)
      sim
    in
    {dlts = best_DLTS_abstraction.dlts; simulation = new_sim}


  let integer_spectrum_abstraction srk tr_matrix simulation = 
    let open Linear in
    let dims =
      SrkUtil.Int.Set.union
        (QQMatrix.row_set tr_matrix)
        (QQMatrix.column_set tr_matrix)
      |> SrkUtil.Int.Set.elements
    in
    let rsd = Linear.rational_spectral_decomposition tr_matrix dims in
    let int_eig_vecs, non_int_eig_vecs =
      BatList.fold_left (fun (int_eig_vecs, non_int_eig_vecs) (lambda, v) ->
        match QQ.to_zz lambda with 
          Some _ -> (v :: int_eig_vecs, non_int_eig_vecs)
        | None -> (int_eig_vecs, v :: non_int_eig_vecs)
        )
        ([], [])
        rsd
    in
    let new_simulation_mat =
      let simulation_mat =
        Array.to_list simulation
        |> List.map (Linear.linterm_of srk)
        |> QQMatrix.of_rows
      in
      let int_eigenspace = QQMatrix.of_rows int_eig_vecs in
      let int_eigenspace_sim =
        Linear.QQVectorSpace.simplify
          (Linear.QQVectorSpace.of_matrix (QQMatrix.mul int_eigenspace simulation_mat))
        |> QQMatrix.of_rows
      in
      match Linear.divide_right int_eigenspace_sim simulation_mat with
      | Some mS' -> mS'   (* simpl(ES) = mS' * mS*)
      | None -> assert false
    in
    let dom_constraints_lhs = compose_simulation srk (QQMatrix.of_rows non_int_eig_vecs) simulation in
    let constraints = BatArray.fold_left (fun f term -> mk_and srk [f; mk_eq srk (mk_zero srk) term]) (mk_true srk) dom_constraints_lhs in
    let new_simulation = compose_simulation srk new_simulation_mat simulation in
    (* new dynamics matrix N, rep matrix M, simulation matrix S: N S = S M  *)
    let sm = QQMatrix.mul new_simulation_mat tr_matrix in 
    match Linear.divide_right sm new_simulation_mat with 
      None -> assert false 
    | Some mat -> constraints, mat, new_simulation
    
    let terminating_conditions_of_formula_via_xseq srk tf =
      let tf = TF.linearize srk tf in
      logf "\nTransition formula:\n%a\n\n" (Formula.pp srk) (TF.formula tf);
      match Smt.is_sat srk (TF.formula tf) with
      | `Sat ->
        let best_DLTS_abstraction = DLTSPeriodicRational.abstract_rational srk tf in
        let m = compute_rep_matrix best_DLTS_abstraction in
        logf "Representation matrix of best Q-DLTS abstraction: %a" Linear.QQMatrix.pp m;
        let constraints, new_dynamics_mat, new_simulation = integer_spectrum_abstraction srk m best_DLTS_abstraction.simulation in
        logf "integrality constraints: %a" (Formula.pp srk) constraints;
        logf "New dynamics matrix: %a" Linear.QQMatrix.pp new_dynamics_mat;
        let best_DLTS_abstraction = {dlts = Lts.PartialLinearMap.make new_dynamics_mat []; simulation = new_simulation } in
        let exp_poly = compute_exp_polynomial new_dynamics_mat in
        let invariant_symbols, inv_equalities, invariant_symbol_set =
          build_symbols_for_inv_terms srk new_simulation
        in
        let invariant_terms = BatList.map (fun symbol -> mk_const srk symbol) invariant_symbols in
        let abstraction = (invariant_symbols, invariant_terms, best_DLTS_abstraction) in
        let formula = mk_and srk [TF.formula tf; mk_and srk inv_equalities; constraints] in
        logf "\nTransition formula with simulation terms:\n%s\n\n" (Formula.show srk formula);
        let ground_formula = Quantifier.mbp srk (fun s -> Symbol.Set.mem s invariant_symbol_set) formula in 
        logf "Formula after model-based projection: %a" (Formula.pp srk) ground_formula;
        let no_floor = SrkSimplify.purify_floor srk ground_formula in
        logf "Formula after removing floors: %a" (Formula.pp srk) no_floor;
        let algebra = function 
        | `Tru -> seq_of_true srk
        | `Fls -> seq_of_false srk
        | `And xs -> seq_and srk xs
        | `Or xs -> seq_or srk xs
        | `Not x -> seq_not srk x
        | `Quantify _ -> failwith "should not see quantifiers in the TF"
        | `Atom (op, s, t) -> 
          begin
            match SrkSimplify.simplify_integer_atom srk op s t with 
              `CompareZero (op, vec) -> seq_of_compare_zero_atom srk op vec exp_poly abstraction
              | `Divides (divisor, vec) -> seq_of_divides_atom srk divisor vec exp_poly abstraction
              | `NotDivides (divisor, vec) ->seq_of_notdivides_atom srk divisor vec exp_poly abstraction
          end
        | `Proposition _ -> failwith "should not see proposition in the TF"
        | `Ite _ -> failwith "should not see ite in the TF"
      in
      logf "start computing char sequence ...";
      let xseq = Formula.eval srk algebra no_floor in 
      logf "finished computing char sequence!";
      let results_in_inv_terms = seq_conditions srk xseq in 
      let results = rewrite_term_condition srk best_DLTS_abstraction.simulation invariant_symbols results_in_inv_terms in
        logf "terminating conditions after rewrite: %a" (Formula.pp srk) results;
        mk_not srk results
      | `Unknown -> failwith "SMT solver should not return unknown for QRA formulas"
      | `Unsat -> (logf ~attributes:[`Bold; `Green] "Transition formula UNSAT, done"); mk_false srk
    

end
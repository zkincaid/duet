open Syntax
open SolvablePolynomial
open BatPervasives
open Sequence

module Vec = Linear.QQVector
module Mat = Linear.QQMatrix
module TF = TransitionFormula

include Log.Make(struct let name = "TerminationDTA" end)

(** Create symbols that stands for some linear terms and their defining
    equalities.
*)
let build_symbols_for_sim_terms srk sim_terms =
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
      sim_terms
      ([], [], Symbol.Set.empty )

(* Compute the representation matrix of a DLTS that contains domain information *)
let compute_rep_matrix best_dlts = 
  let module PLM = Lts.PartialLinearMap in
  let omega_domain = snd (PLM.iteration_sequence best_dlts.dlts) in
  let rep = PLM.map (PLM.make (PLM.map best_dlts.dlts) omega_domain) in
  rep

type ineq_type = Lt0 | Eq0 | Leq0

(** This data structure is used to store a term in an exponential polynomial.
    The key type is a pair (lambda, d) representing term lambda^k * k^d.
    Ordering on the keys is the lexicographic ordering, and values are vectors
    that represent linear terms. For example, a term 
    2^k  (k^3) * (2x + y + z) is stored as 
    an entry with key (2, 3) and value (2, 1, 1).
*)
module BaseDegPairMap = struct
  module QQV = Linear.QQVector
  type pair = QQ.t * int
  module E = SparseMap.Make(struct type t = pair
                            let compare (lambda1, d1) (lambda2, d2) = 
                              if not (QQ.equal lambda1 lambda2) then 
                                QQ.compare lambda1 lambda2
                            else 
                                d1 - d2 
                            end)(QQV)
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

  (** Rank the items in the data structure according to dominance ordering and
      produce a formula that is eventually always true.
      p: the Abelian group map.
      sim_terms: these are the linear terms whose closed forms are computed
          during the symbolic exponentiation of transition matrix. This is 
          used to interpret the meaning of the vectors as values in the map.
      lhs_const: the constant that appears in the closed form formula.
      ineq_type: whether this inequality is <=, = or <.
  *)
  let rank srk p sim_terms ineq_type =
    logf "entering rank";
    let dim_to_term = fun d -> if d < 0 then mk_one srk else BatList.nth sim_terms d in
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
        (E.enum p)
    in
    let conditions = 
      logf "start printing conditions list and formula stems";
      let conditions_list_final, formula_stem_list = 
        BatList.fold_left
          (fun (conditions_list, formula_stem) (_, _, qqt)  ->
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
                 (current_condition :: conditions_list, updated_stem)
                 (** the term being considered is dominated by constant *)
               end
          )
          ([], [])
          dom_ranked_list
      in
      match ineq_type with
      | Lt0  -> 
        mk_or srk conditions_list_final
      | Eq0 -> 
        mk_and srk formula_stem_list
      | Leq0 ->         
        mk_or srk ( (mk_and srk formula_stem_list) :: conditions_list_final)
    in
    conditions
end

(** We obtained the termination condition in terms of some linear terms.
    Now we need to rewrite it into a formula of state variables.
    simulation: the linear terms in the DLTS abstraction
    sim_symbols: aux symbols that we have defined for these terms
    formula: the conditions to be rewritten
*)
let rewrite_term_condition srk simulation sim_symbols formula =
  let m = BatList.fold_lefti
      (fun m i inv_symb -> 
         Symbol.Map.add inv_symb (BatArray.get simulation i) m
      )
      Symbol.Map.empty
      sim_symbols
  in
  substitute_map srk m formula

(* Compose two simulations mS and sim, where mS is a matrix and sim is an array of linear terms *)
let compose_simulation srk mS simulation =
  Linear.QQMatrix.rowsi mS
  /@ (fun (_, row) ->
    Linear.term_of_vec srk (fun i -> simulation.(i)) row
    |> SrkSimplify.simplify_term srk)
  |> BatArray.of_enum

(** For a linear term, get its vector representation w.r.t. a list of symbols. 
    For example, x + 2z + 1 w.r.t. [x, y, z] is represented by a tuple 
    containing a vector and the constant term:
      ([1, 0, 2], 1)
    *)
let rewrite_exp_under_basis expression list_symbols = 
  let vec = 
    BatList.fold_lefti
      (fun existing_coeffs i symbol -> 
          let coeff = Vec.coeff (Linear.dim_of_sym symbol) expression in
          Vec.add_term coeff i existing_coeffs 
      )
      Vec.zero
      list_symbols
  in
  let const = Vec.coeff CoordinateSystem.const_id expression in
  Vec.add_term const (-1) vec
  (* (vec, const) *)

(* Scale a simulation such that it maps integer states to integer states *)
let scale_simulation srk best_DLTS_abstraction = 
  let sim = best_DLTS_abstraction.simulation in 
  let lcm_of_denominators = BatArray.fold_left 
    (fun d term -> 
      let coeff_vec = Linear.linterm_of srk term in
      ZZ.lcm 
        d 
        (BatEnum.fold 
          (fun dd (coeff, _) -> ZZ.lcm dd (QQ.denominator coeff)) 
          ZZ.one
          (Linear.QQVector.enum coeff_vec))
    ) 
    ZZ.one 
    sim 
  in
  let new_sim = BatArray.map (fun orig_term -> 
    let coeff_vec = Linear.linterm_of srk orig_term in 
    let new_vec = Linear.QQVector.scalar_mul (QQ.of_zz lcm_of_denominators) coeff_vec in 
    Linear.of_linterm srk new_vec)
    sim
  in
  {dlts = best_DLTS_abstraction.dlts; simulation = new_sim}

(* Compute the integer spectrum restriction of a DLTS that contains a new dynamics matrix and
   domain restrictions. *)
let integer_spectrum_abstraction srk tr_matrix simulation = 
  let open Linear in
  let dims =
    SrkUtil.Int.Set.union
      (QQMatrix.row_set tr_matrix)
      (QQMatrix.column_set tr_matrix)
    |> SrkUtil.Int.Set.elements
  in
  let rsd = Linear.rational_spectral_decomposition tr_matrix dims in

  let int_eig_vecs, non_int_eig_vecs = BatList.partition (fun (lambda, _) -> ZZ.equal (QQ.denominator lambda) ZZ.one ) rsd in
  let int_eig_vecs = BatList.map (fun (_, v) -> v) int_eig_vecs in
  let non_int_eig_vecs = BatList.map (fun (_, v) -> v) non_int_eig_vecs in
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
  let constraints = mk_and srk (List.map (mk_eq srk (mk_zero srk)) (BatArray.to_list dom_constraints_lhs)) in
  let new_simulation = compose_simulation srk new_simulation_mat simulation in
  (* new dynamics matrix N, rep matrix M, and simulation matrix S satisfy N S = S M *)
  let sm = QQMatrix.mul new_simulation_mat tr_matrix in 
  match Linear.divide_right sm new_simulation_mat with 
    None -> assert false 
  | Some mat -> constraints, mat, new_simulation

(* 
   Characteristic sequence related operations 

   A characteristic sequence S is a periodic sequence of formulas that encodes the 
   long-time dynamics of an LIA formula G with respect to dynamics matrix A. 
   Specifically, we have that for k sufficiently large, G(A^k x) = S_k.
*)
module XSeq = struct

  let seq_of_true srk =
    Periodic.make [mk_true srk]

  let seq_of_false srk =
    Periodic.make [mk_false srk]
    
  (* let seq_and srk x y = 
    Periodic.map2 (fun a b -> mk_and srk [a; b]) x y *)

  let seq_and srk xs =
    Periodic.mapn (mk_and srk) xs
  
  (* let seq_or srk x y =
    Periodic.map2 (fun a b -> mk_or srk [a; b]) x y *)

  let seq_or srk xs =
    Periodic.mapn (mk_or srk) xs

  let seq_add_term srk x y =
    Periodic.map2 (fun a b -> mk_add srk [a; b]) x y

  let seq_add_int x y =
    Periodic.map2 (fun a b -> a + b) x y

  let seq_add_qq x y =
    Periodic.map2 (fun a b -> QQ.add a b) x y

  let seq_mul_symbol srk x symbol =
    Periodic.map (fun t -> mk_mul srk [mk_real srk t; mk_const srk symbol]) x

  let seq_not srk x = 
    Periodic.map (fun f -> mk_not srk f) x

  (* seq_of_exp m t returns the characteristic sequence of t^k mod m, 
  k = 0, 1, 2, ... *)
  let seq_of_exp modulus lambda = 
    UltimatelyPeriodic.unfold (fun power -> (power * lambda) mod modulus) 1 
    |> periodic_approx


  (* seq_of_polynomial srk m p returns characteristic sequence of p(k) mod m, 
  k = 0, 1, 2, ... *)
  let seq_of_polynomial modulus poly = 
    if Polynomial.QQX.order poly = 0 then 
      Periodic.make [QQ.modulo (Polynomial.QQX.eval poly QQ.zero) (QQ.of_int modulus)]
    else
    let lcm_of_denoms =
      BatEnum.fold (fun current_lcm (coeff, _) -> ZZ.lcm current_lcm (QQ.denominator coeff)) 
      ZZ.one
      (Polynomial.QQX.enum poly)
    in
    (* let poly = Polynomial.QQX.scalar_mul (QQ.of_zz lcm_of_denoms) poly in *)
    let period = modulus * (BatOption.get (ZZ.to_int lcm_of_denoms)) in
    (0 -- (period - 1))
    /@ (fun i -> QQ.modulo (Polynomial.QQX.eval poly (QQ.of_int i)) (QQ.of_int modulus))
    |> BatList.of_enum
    |> Periodic.make

  (* seq_of_polynomial srk m p b returns characteristic sequence of b^k p(k) mod m, 
  k = 0, 1, 2, ... *)
  let seq_of_single_base_exp_polynomial modulus poly base =
    let seq_of_exp = seq_of_exp modulus base in
    let seq_of_poly = seq_of_polynomial modulus poly in
    Periodic.map2 
      (fun n p -> QQ.modulo (QQ.mul (QQ.of_int n) p) (QQ.of_int modulus))
      seq_of_exp
      seq_of_poly

  (* characteristic sequence of an exponential polynomial modulo some number *)
  let seq_of_exp_polynomial modulo exppoly =
    BatEnum.fold 
      (fun existing_seq (poly, base) -> 
        let b = match QQ.to_zz base with 
          Some i -> BatOption.get (ZZ.to_int (ZZ.modulo i (ZZ.of_int modulo)))
          | None -> failwith "Non-integer base in the exponential polynomial"
        in
        let current_seq = seq_of_single_base_exp_polynomial modulo poly b in 
          seq_add_qq existing_seq current_seq
      )
    (Periodic.make [QQ.zero])
    (ExpPolynomial.enum exppoly)
  
  (* Compute characteristic sequence of atomic formulas LHS < 0, LHS = 0, LHS <= 0. 
     LHS has form c^T x < 0, c^T x <= 0, or c^T x = 0. 
      op: <, <=, =
      vec: coefficients vector c
      exp_poly: gives A^k x where A is the dynamics matrix, so that we get to compute 
          c^T A^k x as an exponential polynomial in k
  *)
  let seq_of_compare_zero_atom srk op vec exp_poly abstraction =
    let ineq_type, lhs = match op with
      | `Lt -> Lt0, vec
      | `Eq -> Eq0, vec
      | `Leq -> Leq0, vec
    in 
    let (sim_symbols, sim_terms) = abstraction in
    let lt_vec = rewrite_exp_under_basis lhs sim_symbols in
    logf "\nlt_vec is: %a" Vec.pp lt_vec;
    let lt_vec_exppoly = ExpPolynomial.Vector.of_qqvector lt_vec in
    let closed_form_vec = ExpPolynomial.Matrix.vector_left_mul lt_vec_exppoly exp_poly in
    (* check if the dynamic matrix has negative eigenvalues *)
    let has_negative_base = BatEnum.exists 
        (fun (entry, _) -> 
            BatEnum.exists 
              (fun (_, base) -> QQ.lt base QQ.zero)
              (ExpPolynomial.enum entry)
        )
        (ExpPolynomial.Vector.enum closed_form_vec)
    in
    let analyze_entries entries =
      begin
        logf "start iterating entries";
        let m = BaseDegPairMap.put (QQ.one, 0) (Vec.coeff (-1) vec) (-1) BaseDegPairMap.empty in
        let m = BatEnum.fold 
            ( fun m (entry, idx) ->                
                logf "iterating this entry: %a at coordinate: %d" ExpPolynomial.pp entry idx;
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
                          BaseDegPairMap.put index_pair coeff idx m
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
        let conditions = BaseDegPairMap.rank srk m sim_terms ineq_type in
        logf "ultimately invariant formula: %a" (Formula.pp srk) conditions;
        conditions
      end
    in
    if has_negative_base then
      begin
        logf "Dynamic matrix has negative eigenvalues, computing length-2 char sequence...";
        let entries_with_even_exp = BatEnum.map (
            fun (entry, i) -> 
              let t = ExpPolynomial.compose_left_affine entry 2 0 in
              (t, i)
          ) 
          (ExpPolynomial.Vector.enum closed_form_vec) 
        in
        let sat_even_conditions = analyze_entries entries_with_even_exp in
        (* let sat_even_conditions = rewrite_term_condition srk best_DLTS_abstraction.simulation sim_symbols sat_even_conditions' in *)
        (* logf "sat_even conditions: %a" (Formula.pp srk) (rewrite_term_condition srk best_DLTS_abstraction.simulation sim_symbols sat_even_conditions');  *)
        let entries_with_odd_exp = BatEnum.map (
            fun (entry, i) -> 
              let t = ExpPolynomial.compose_left_affine entry 2 1 in
              (t, i)
          ) 
          (ExpPolynomial.Vector.enum closed_form_vec) 
        in
        let sat_odd_conditions = analyze_entries entries_with_odd_exp in
        (* let sat_odd_conditions = rewrite_term_condition srk best_DLTS_abstraction.simulation sim_symbols sat_odd_conditions in *)
        (* logf "sat_odd conditions: %a" (Formula.pp srk) (rewrite_term_condition srk best_DLTS_abstraction.simulation sim_symbols sat_odd_conditions);  *)
        let results = Periodic.make [SrkSimplify.simplify_terms srk sat_even_conditions; SrkSimplify.simplify_terms srk sat_odd_conditions] in
        results
      end
    else
      begin
        let mat_entries = ExpPolynomial.Vector.enum closed_form_vec in
        let res = analyze_entries mat_entries in 
        Periodic.make [SrkSimplify.simplify_terms srk res]
      end

  (* Compute characteristic sequence of atom q | w^T A^k x. 
     zz_divisor: represents divisor q
     dividend_vec: linear term of state variables
     exp_poly: closed form of A^k x
  *)
  let seq_of_divides_atom srk zz_divisor dividend_vec exp_poly abstraction =
    let divisor = match ZZ.to_int zz_divisor with
      | Some i -> i
      | None -> failwith "see non-integer divisor, error"
    in
    let (sim_symbols, _) = abstraction in
    let lt_vec = rewrite_exp_under_basis dividend_vec sim_symbols in
    logf "\nlt_vec is: %a" Vec.pp lt_vec;
    let lt_vec_exppoly = ExpPolynomial.Vector.of_qqvector lt_vec in
    let closed_form_dividend =
      (ExpPolynomial.Matrix.vector_left_mul lt_vec_exppoly exp_poly)
    in
    let dividend_xseqs =
      BatEnum.fold
        (fun existing_seq (exppoly, dim) ->
          let current_seq =
            seq_mul_symbol srk
              (seq_of_exp_polynomial divisor exppoly)
              (List.nth sim_symbols dim)
          in
          seq_add_term srk existing_seq current_seq)
        (Periodic.make [mk_real srk (Vec.coeff (-1) dividend_vec)])
        (ExpPolynomial.Vector.enum closed_form_dividend)
    in
    let mk_divides t =
      mk_eq srk (mk_mod srk t (mk_real srk (QQ.of_int divisor))) (mk_zero srk)
    in
    Periodic.map mk_divides dividend_xseqs

  let seq_of_notdivides_atom srk zz_divisor dividend_vec exp_poly abstraction =
    seq_of_divides_atom srk zz_divisor dividend_vec exp_poly abstraction
    |> seq_not srk
  
  let omega_dom_basis_mat dim omega_dom_mat =
    let g = Linear.nullspace omega_dom_mat (BatList.init dim (fun i -> i) ) in
    let g = Linear.QQVectorSpace.simplify g in
    Linear.QQMatrix.transpose (Linear.QQMatrix.of_rows g)

  let tr_mat_restricted_to_omega_dom tr_mat omega_dom_basis_mat =
    BatOption.get (Linear.divide_left (Linear.QQMatrix.mul tr_mat omega_dom_basis_mat) omega_dom_basis_mat)

  let int_spec_abstraction nb_cols_omega_dom_basis_mat tr_omega =
    let open Linear in
    let t = QQMatrix.transpose tr_omega in 
    let dims = (BatList.init nb_cols_omega_dom_basis_mat (fun i -> i) ) in
    let rsd = rational_spectral_decomposition t dims in
  let int_eig_vecs, _ = BatList.partition (fun (lambda, _) -> ZZ.equal (QQ.denominator lambda) ZZ.one ) rsd in
  let int_eig_vecs = BatList.map (fun (_, v) -> v) int_eig_vecs in
  let int_eig_vecs = Linear.QQVectorSpace.simplify int_eig_vecs in
  (* let non_int_eig_vecs = BatList.map (fun (_, v) -> v) non_int_eig_vecs in *)
  let g' = QQMatrix.transpose (QQMatrix.of_rows int_eig_vecs) in
  g'
    
  let tr_mat_restricted_to_int_dom tr_mat g g' =
    let gg' = Linear.QQMatrix.mul g g' in
    BatOption.get (Linear.divide_left (Linear.QQMatrix.mul tr_mat gg') gg')

  let build_symbols_for_gg'_cols srk gg' = 
    let nb_cols = Linear.QQMatrix.nb_columns gg' in 
    let list_symbols = BatList.init nb_cols (fun i -> 
      let name_str = String.concat "_" ["dta"; "term"; (string_of_int i)] in
      let symbol = mk_symbol srk ~name:name_str `TyInt in
      symbol
    ) in 
    list_symbols

  let build_eqs_for_dta_terms srk list_dta_symbols gg' simulation =
    BatArray.fold_lefti (fun eqs i sim_term ->
      let row = Linear.QQMatrix.row i gg' in 
      (mk_eq srk 
       (Linear.term_of_vec srk (fun j -> (mk_const srk (BatList.nth list_dta_symbols j))) row )
        sim_term
      ) :: eqs )
      []
      simulation

  (* Compute a mortal precondition of a transition formula through characteristic sequences. *)  
  let terminating_conditions_of_formula_via_xseq srk tf =
    logf "DTA starts";
    let tf = TF.linearize srk tf in
    logf "\nTransition formula linearized:\n%a\n\n" (Formula.pp srk) (TF.formula tf);
    match Smt.is_sat srk (TF.formula tf) with
    | `Sat ->
      let best_DLTS_abstraction = DLTSPeriodicRational.abstract_rational srk tf in
      logf "finished computing best DLTS abstraction";
      let best_DLTS_abstraction = scale_simulation srk best_DLTS_abstraction in
      logf "finished scaling up simulation";
      (* let m = compute_rep_matrix best_DLTS_abstraction in *)
      (* logf "Representation matrix of best Q-DLTS abstraction: %a" Linear.QQMatrix.pp m; *)
      let module PLM = Lts.PartialLinearMap in
      let omega_domain = snd (PLM.iteration_sequence best_DLTS_abstraction.dlts) in
      let omega_dom_mat = Linear.QQMatrix.of_rows omega_domain in
      let dim = BatArray.length best_DLTS_abstraction.simulation in
      let g = omega_dom_basis_mat dim omega_dom_mat in
      let tr = PLM.map best_DLTS_abstraction.dlts in
      let tr_omega = tr_mat_restricted_to_omega_dom tr g in
      let g' = int_spec_abstraction (Linear.QQMatrix.nb_columns g) tr_omega in
      let tr_z = tr_mat_restricted_to_int_dom tr g g' in
       logf "Dynamics matrix in restricted space: %a" Linear.QQMatrix.pp tr_z;
      (* exists x, x'. F(x, x') /\ G G' z = S x *)
      let gg' = (Linear.QQMatrix.mul g g') in
      let list_dta_symbols = build_symbols_for_gg'_cols srk gg' in
      let dta_terms_eqs = build_eqs_for_dta_terms srk list_dta_symbols gg' best_DLTS_abstraction.simulation in
      let formula = mk_and srk [TF.formula tf; mk_and srk dta_terms_eqs] in
      let dta_symbols_set = Symbol.Set.of_list list_dta_symbols in
      let ground_formula = Quantifier.mbp srk (fun s -> Symbol.Set.mem s dta_symbols_set) formula in 
      logf "Formula after model-based projection: %a" (Formula.pp srk) ground_formula;
      let no_floor = SrkSimplify.eliminate_floor srk ground_formula in
      logf "Formula after removing floors: %a" (Formula.pp srk) no_floor;
      let exp_poly = BatOption.get (ExpPolynomial.exponentiate_rational tr_z) in
      let abstraction = (list_dta_symbols, (BatList.map (fun s -> mk_const srk s) list_dta_symbols)) in
      let algebra = function 
      | `Tru -> seq_of_true srk
      | `Fls -> seq_of_false srk
      | `And xs -> seq_and srk xs
      | `Or xs -> seq_or srk xs
      | `Not x -> seq_not srk x
      | `Quantify _ -> failwith "should not see quantifiers in the TF"
      | `Atom (op, s, t) -> 
        begin
          logf "processing atomic formula";
          match SrkSimplify.simplify_integer_atom srk op s t with 
              `CompareZero (op, vec) -> logf "compare zero formula"; seq_of_compare_zero_atom srk op vec exp_poly abstraction
            | `Divides (divisor, vec) -> logf "divides formula"; seq_of_divides_atom srk divisor vec exp_poly abstraction
            | `NotDivides (divisor, vec) -> logf "Not divides formula"; seq_of_notdivides_atom srk divisor vec exp_poly abstraction
        end
      | `Proposition _ -> failwith "should not see proposition in the TF"
      | `Ite _ -> failwith "should not see ite in the TF"
    in
    logf "start computing char sequence ...";
    let xseq = Formula.eval srk algebra no_floor in 
    logf "finished computing char sequence!";
    let results_in_dta_terms = mk_and srk (Periodic.period xseq) in 
    (* let results = rewrite_term_condition srk best_DLTS_abstraction.simulation sim_symbols results_in_sim_terms in *)
    let results = SrkSimplify.simplify_terms srk results_in_dta_terms in
    let results = mk_and srk (results::dta_terms_eqs) in
      logf "terminating conditions after rewrite: %a" (Formula.pp srk) results;
      results
    | `Unknown -> failwith "SMT solver should not return unknown for QRA formulas"
    | `Unsat -> (logf ~attributes:[`Bold; `Green] "Transition formula UNSAT, done"); mk_false srk
end



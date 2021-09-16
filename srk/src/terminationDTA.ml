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
         let symbol = mk_symbol srk ~name:name_str (expr_typ srk term) in
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

(** Linear terms with exponential-polynomial coefficients, represented
   as an exponential polynomial with linear term coefficients. *)
(** This data structure is used to store a term in an exponential
   polynomial.  The key type is a pair (lambda, d) representing term
   lambda^k * k^d.  Ordering on the keys is lexicographic reversed
   ordering (e.g., (5/2,2) < (2,3) < (2,1) < ...), and values are
   vectors that represent linear terms. For example, a term 2^k (k^3)
   * (2x + y + z) is stored as an entry with key (2, 3) and value (2,
   1, 1).  If all lambdas are >= 0, the ording coincides with
   asymptotic dominance ordering. *)
module EPTerm = struct
  (* An exponential-polynomial term
      lambda_1^k * k^d_1 * v_1 + ... + lambda_n^k * k^d_n * v_n
    where each v_i is a linear term is represented as a map
    [ (lambda_1, d_1) -> v_1, ..., (lambda_n, d_n) -> v_n ]
    Ordering on (lambda, d) keys is lexicographic; assuming lambda_i's
    are positive, this coincides with dominance order. *)
  module E = SparseMap.Make
               (struct
                 type t = QQ.t * int
                 let compare (lambda1, d1) (lambda2, d2) =
                   match QQ.compare lambda2 lambda1 with
                   | 0 -> d2 - d1
                   | cmp -> cmp
               end)
               (Vec)
  type t = E.t
  let empty = E.zero

  (* Shared logic of eventually_positive / eventually_nonnegative:
     they differ only on whether 0 satsifes (nonnegative) or does not
     satisfy (positive) the predicate. *)
  let _eventually z srk p f =
    let zero = mk_zero srk in
    let rec go e =
      match BatEnum.get e with
      | Some (_, vec) ->
         let t = Linear.term_of_vec srk f vec in
         mk_or srk [mk_lt srk zero t;
                    mk_and srk [mk_eq srk zero t; go e]]
      | None -> z
    in
    go (E.enum p)

  let eventually_positive srk = _eventually (mk_false srk) srk
  let eventually_nonnegative srk = _eventually (mk_true srk) srk

  let is_zero srk p f =
    let zero = mk_zero srk in
    (E.enum p)
    /@ (fun (_, vec) -> mk_eq srk zero (Linear.term_of_vec srk f vec))
    |> BatList.of_enum
    |> mk_and srk

  (** Given a vector of exponentials ep_vec and a constant k representing the term
        k + ep_vec(0) * x0 + ep_vec(1) * e1 + ... + ep_vec(n) * xn
      compute a representation of this term as an EPTerm *)
  let of_ep_vec ep_vec =
    BatEnum.fold
      (fun ep_term (ep, dim) ->
        BatEnum.fold
          (fun ep_term (poly, base) ->
            BatEnum.fold
              (fun ep_term (coeff, degree) ->
                E.modify (base, degree) (Vec.add_term coeff dim) ep_term)
              ep_term
              (Polynomial.QQX.enum poly))
          ep_term
          (ExpPolynomial.enum ep))
      empty
      (ExpPolynomial.Vector.enum ep_vec)
end

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

  let seq_and srk xs =
    Periodic.mapn (mk_and srk) xs

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
  let seq_of_compare_atom srk op closed_form_vec term_of_dim =
    (* Even/odd case split to avoid negative exponentials, if needed *)
    let positive_cf =
      (* Does closed_form_vec have a negative exponential? *)
      let has_negative_base =
        BatEnum.exists
          (fun (entry, _) ->
            BatEnum.exists
              (fun (_, base) -> QQ.lt base QQ.zero)
              (ExpPolynomial.enum entry))
          (ExpPolynomial.Vector.enum closed_form_vec)
      in
      if has_negative_base then
        let cf_even =
          ExpPolynomial.Vector.map
            (fun _ ep -> ExpPolynomial.compose_left_affine ep 2 0)
            closed_form_vec
        in
        let cf_odd =
          ExpPolynomial.Vector.map
            (fun _ ep -> ExpPolynomial.compose_left_affine ep 2 1)
            closed_form_vec
        in
        Periodic.make [cf_even; cf_odd]
      else
        Periodic.make [closed_form_vec]
    in
    positive_cf
    |> Periodic.map (fun ep_vec ->
           let ep_term = EPTerm.of_ep_vec ep_vec in
           match op with
           | `Pos -> EPTerm.eventually_positive srk ep_term term_of_dim
           | `Nonneg -> EPTerm.eventually_nonnegative srk ep_term term_of_dim
           | `Zero -> EPTerm.is_zero srk ep_term term_of_dim)

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
      mk_eq
        srk
        (mk_mod srk t (mk_real srk (QQ.of_int divisor)))
        (mk_zero srk)
    in
    Periodic.map mk_divides dividend_xseqs

  let seq_of_notdivides_atom srk zz_divisor dividend_vec exp_poly abstraction =
    seq_of_divides_atom srk zz_divisor dividend_vec exp_poly abstraction
    |> seq_not srk

  (* Compute a matrix G such that Gx for all vector x spans the omega domain.
     The columns of G form a basis for the omega domain.
  *)
  let omega_dom_basis_mat dim omega_dom_mat =
    let g = Linear.nullspace omega_dom_mat (BatList.init dim (fun i -> i) ) in
    let g = Linear.QQVectorSpace.simplify g in
    Linear.QQMatrix.transpose (Linear.QQMatrix.of_rows g)

  (* Compute a transition matrix M that represents the linear mapping restricted to the omega domain.
     Let the original transition matrix be T, and the matrix whose columns form a basis for the omega
     domain be G. Then we must have GM = TG according to the following diagram
          M
     x   -->   Mx        (omega domain)
     |         |
     Gx  -->   GMx=TGx   (original domain)
          T

  *)
  let tr_mat_restricted_to_omega_dom tr_mat omega_dom_basis_mat =
    BatOption.get (Linear.divide_left (Linear.QQMatrix.mul tr_mat omega_dom_basis_mat) omega_dom_basis_mat)

  (* Compute the integer spectrum restriction of a transition matrix.
     This computes a matrix G' such that G'z for all z spans the integer domain on which the
     state of the linear mapping always consists of integer vectors.
  *)
  let int_spec_abstraction nb_cols_omega_dom_basis_mat tr_omega =
    let open Linear in
    let t = QQMatrix.transpose tr_omega in
    let dims = (BatList.init nb_cols_omega_dom_basis_mat (fun i -> i) ) in
    let rsd = rational_spectral_decomposition t dims in
    let int_eig_vecs, _ = BatList.partition (fun (lambda, _) -> ZZ.equal (QQ.denominator lambda) ZZ.one ) rsd in
    let int_eig_vecs = BatList.map (fun (_, v) -> v) int_eig_vecs in
    let int_eig_vecs = Linear.QQVectorSpace.simplify int_eig_vecs in
      QQMatrix.transpose (QQMatrix.of_rows int_eig_vecs)

  (* Further restricting the linear mapping to the integer domain, from which all states always remain integers.
     This is achieved by solving for M in GG' M = T GG'.
  *)
  let tr_mat_restricted_to_int_dom tr_mat g g' =
    let gg' = Linear.QQMatrix.mul g g' in
    BatOption.get (Linear.divide_left (Linear.QQMatrix.mul tr_mat gg') gg')

  (* Build a symbol for each column of GG'. *)
  let build_symbols_for_gg'_cols srk gg' =
    let nb_cols = Linear.QQMatrix.nb_columns gg' in
    let list_symbols = BatList.init nb_cols (fun i ->
      let name_str = String.concat "_" ["dta"; "term"; (string_of_int i)] in
      let symbol = mk_symbol srk ~name:name_str `TyInt in
      symbol
    ) in
    list_symbols

  (* Tries to encode GG' x = S x, where S is the (composed) simulation function. *)
  let build_eqs_for_dta_terms srk list_dta_symbols gg' simulation =
    BatArray.fold_lefti (fun eqs i sim_term ->
      let row = Linear.QQMatrix.row i gg' in
      (mk_eq srk
        (Linear.term_of_vec srk (fun j -> (mk_const srk (BatList.nth list_dta_symbols j))) row)
        sim_term
      ) :: eqs)
      []
      simulation

  (* Given: a sparse affine term t(x) (dimensions correspond to
     symbols), a list of symbols [x] defining a finite-dimensional
     subspace and a matrix exponential M^k in this subspace, compute
     t(M^k(x)), represented as an (affine) vector wrt the basis
     [x]. *)
  let closed_form sim_symbols linterm ep_mat =
    (* Subtract constant coordinate & add it back to the closed form later *)
    let (const, vec) =
      Vec.pivot Linear.const_dim (rewrite_exp_under_basis linterm sim_symbols)
    in
    ExpPolynomial.Matrix.vector_left_mul (ExpPolynomial.Vector.of_qqvector vec) ep_mat
    |> ExpPolynomial.Vector.add_term (ExpPolynomial.scalar const) Linear.const_dim

  (* Compute a mortal precondition of a transition formula through characteristic sequences. *)
  let terminating_conditions_of_formula_via_xseq srk tf =
    logf "DTA starts";
    let tf = TF.linearize srk tf in
    logf "\nTransition formula linearized:\n%a\n\n" (Formula.pp srk) (TF.formula tf);
    match Smt.is_sat srk (TF.formula tf) with
    | `Sat ->
       let best_DLTS_abstraction =
         DLTSPeriodicRational.abstract_rational srk tf
         |> DLTS.simplify srk ~scale:true
       in
      logf "finished computing best DLTS abstraction";
      let module PLM = Lts.PartialLinearMap in
      let omega_domain = snd (PLM.iteration_sequence best_DLTS_abstraction.dlts) in
      let omega_dom_mat = Linear.QQMatrix.of_rows omega_domain in
      let dim = BatArray.length best_DLTS_abstraction.simulation in
      (* Compute matrix G as a basis for omega domain. *)
      let g = omega_dom_basis_mat dim omega_dom_mat in
      let tr = PLM.map best_DLTS_abstraction.dlts in
      let tr_omega = tr_mat_restricted_to_omega_dom tr g in
      (* Compute matrix G' as a basis for integer domain. *)
      let g' = int_spec_abstraction (Linear.QQMatrix.nb_columns g) tr_omega in
      let tr_z = tr_mat_restricted_to_int_dom tr g g' in
       logf "Dynamics matrix in restricted space: %a" Linear.QQMatrix.pp tr_z;
      (* exists x, x'. F(x, x') /\ G G' z = S x *)
      let gg' = (Linear.QQMatrix.mul g g') in
      let list_dta_symbols = build_symbols_for_gg'_cols srk gg' in
      let dta_terms_eqs = build_eqs_for_dta_terms srk list_dta_symbols gg' best_DLTS_abstraction.simulation in
      let formula = mk_and srk [TF.formula tf; mk_and srk dta_terms_eqs] in
      let dta_symbols_set = Symbol.Set.of_list list_dta_symbols in
      let ground_formula = Quantifier.mbp srk (fun s -> Symbol.Set.mem s dta_symbols_set) formula
                           |> SrkSimplify.simplify_dda srk
      in
      logf "Formula after model-based projection: %a" (Formula.pp srk) ground_formula;
      let no_floor = SrkSimplify.eliminate_floor srk ground_formula in
      logf "Formula after removing floors: %a" (Formula.pp srk) no_floor;
      let exp_poly = BatOption.get (ExpPolynomial.exponentiate_rational tr_z) in
      let abstraction = (list_dta_symbols, (BatList.map (fun s -> mk_const srk s) list_dta_symbols)) in
      let term_of_dim i =
        if i == Linear.const_dim then mk_one srk
        else best_DLTS_abstraction.simulation.(i)
      in
      let algebra = function
      | `Tru -> seq_of_true srk
      | `Fls -> seq_of_false srk
      | `And xs -> seq_and srk xs
      | `Or xs -> seq_or srk xs
      | `Not x -> seq_not srk x
      | `Quantify _ -> failwith "should not see quantifiers in the TF"
      | `Atom (`Arith (op, s, t)) ->
        begin
          match SrkSimplify.simplify_integer_atom srk op s t with
          | `CompareZero (op, vec) ->
             let cf = closed_form list_dta_symbols (Vec.negate vec) exp_poly in
             let predicate = match op with
               | `Eq -> `Zero
               | `Leq -> `Nonneg
               | `Lt -> `Pos
             in
             seq_of_compare_atom srk predicate cf term_of_dim
          | `Divides (divisor, vec) ->
             seq_of_divides_atom srk divisor vec exp_poly abstraction
          | `NotDivides (divisor, vec) ->
             seq_of_notdivides_atom srk divisor vec exp_poly abstraction
        end
      | `Atom (`ArrEq _) -> failwith "should not see ArrEq in the TF"
      | `Proposition _ -> failwith "should not see proposition in the TF"
      | `Ite _ -> failwith "should not see ite in the TF"
    in
    logf "start computing char sequence ...";
    let xseq = Formula.eval srk algebra no_floor in
    logf "finished computing char sequence!";
    let results_in_dta_terms = mk_and srk (Periodic.period xseq) in
    let results = SrkSimplify.simplify_terms srk results_in_dta_terms in
    let results = mk_and srk (results :: dta_terms_eqs) in
      logf "terminating conditions after rewrite: %a" (Formula.pp srk) results;
      results
    | `Unknown -> failwith "SMT solver should not return unknown for QRA formulas"
    | `Unsat -> (logf ~attributes:[`Bold; `Green] "Transition formula UNSAT, done"); mk_false srk
end

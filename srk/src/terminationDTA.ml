open Syntax
open SolvablePolynomial
open BatPervasives
open Sequence

module Vec = Linear.QQVector
module Mat = Linear.QQMatrix
module TF = TransitionFormula

include Log.Make(struct let name = "TerminationDTA" end)

(** Linear terms with exponential-polynomial coefficients, represented
   as an exponential polynomial with linear term coefficients. *)
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

module XSeq = struct
  let seq_of_exp modulus lambda = 
    UltimatelyPeriodic.unfold (fun power -> (power * lambda) mod modulus) 1 
    |> periodic_approx

  let seq_of_polynomial modulus poly = 
    let lcm_of_denoms =
      BatEnum.fold (fun current_lcm (coeff, _) -> ZZ.lcm current_lcm (QQ.denominator coeff))
      ZZ.one
      (Polynomial.QQX.enum poly)
    in
    let poly = Polynomial.QQX.scalar_mul (QQ.of_zz lcm_of_denoms) poly in
    let modulus = modulus * (BatOption.get (ZZ.to_int lcm_of_denoms)) in
    (0 -- (modulus - 1))
    /@ (fun i -> 
        match QQ.to_int (Polynomial.QQX.eval poly (QQ.of_int i)) with
          | Some result -> QQ.of_zzfrac (ZZ.of_int (result mod modulus)) lcm_of_denoms
          | None -> assert false)
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
  let seq_of_exp_polynomial modulus exppoly =
    BatEnum.fold 
      (fun existing_seq (poly, base) -> 
        let b = match QQ.to_zz base with 
          | Some i -> BatOption.get (ZZ.to_int (ZZ.modulo i (ZZ.of_int modulus)))
          | None -> failwith "Non-integer base in the exponential polynomial"
        in
        let current_seq = seq_of_single_base_exp_polynomial modulus poly b in
        let add_mod x y = QQ.modulo (QQ.add x y) (QQ.of_int modulus) in
        Periodic.map2 add_mod existing_seq current_seq)
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
  let seq_of_divides_atom srk zz_divisor closed_form_dividend term_of_dim =
    let divisor = match ZZ.to_int zz_divisor with
      | Some i -> i
      | None -> failwith "see non-integer divisor, error"
    in
    let dividend_xseqs =
      ExpPolynomial.Vector.enum closed_form_dividend
      /@ (fun (exppoly, dim) ->
        let term = term_of_dim dim in
        Periodic.map
          (fun k -> mk_mul srk [mk_real srk k; term])
          (seq_of_exp_polynomial divisor exppoly))
      |> BatList.of_enum
      |> Periodic.mapn (mk_add srk)
    in
    let mk_divides t =
      mk_eq
        srk
        (mk_mod srk t (mk_real srk (QQ.of_int divisor)))
        (mk_zero srk)
    in
    Periodic.map mk_divides dividend_xseqs
end


(* Given a matrix A representing a linear space V = { x : Ax = 0 },
   compute a matrix G whose columns form a basis for V *)
let constraints_to_generators dim constraint_mat =
  let g = Linear.nullspace constraint_mat (BatList.init dim (fun i -> i)) in
  let g = Linear.QQVectorSpace.simplify g in
  Linear.QQMatrix.transpose (Linear.QQMatrix.of_rows g)

(* Given a dynamics matrix T and a matrix G whose columns form a basis
   for an invariant subspace of M, find a compute a matrix
   representation of M restricted to colspace(G) w.r.t. the basis G;
   that is, a matrix R with TG = GR.  I.e.,

          M
     x   -->   Mx        (omega domain)
     |         |
     Gx  -->   GMx=TGx   (original domain)
          T
*)
let inv_subspace_restriction tr inv_subspace =
  BatOption.get (Linear.divide_left (Linear.QQMatrix.mul tr inv_subspace) inv_subspace)

(* Given a dynamics matrix T, compute a matrix G whose columns
   form a basis for the space spanned by the eigenvectors of T
   with integer eigenvalues *)
let int_eigenspace dim t =
  let open Linear in
  rational_spectral_decomposition (QQMatrix.transpose t) (BatList.init dim (fun i -> i))
  |> BatList.filter_map (fun (lambda, v) ->
         if ZZ.equal (QQ.denominator lambda) ZZ.one then Some v
         else None)
  |> Linear.QQVectorSpace.simplify
  |> QQMatrix.of_rows
  |> QQMatrix.transpose

(* Given: a sparse affine term t(x) (dimensions correspond to
   symbols), a list of symbols [x] defining a finite-dimensional
   subspace and a matrix exponential M^k in this subspace, compute
   t(M^k(x)), represented as an (affine) vector wrt the basis [x]. *)
let closed_form sim_symbols linterm ep_mat =
  let vec =
    BatArray.fold_lefti
      (fun vec i symbol -> 
        let coeff = Vec.coeff (Linear.dim_of_sym symbol) linterm in
        ExpPolynomial.Vector.add_term (ExpPolynomial.scalar coeff) i vec)
      ExpPolynomial.Vector.zero
      sim_symbols
  in
  ExpPolynomial.Matrix.vector_left_mul vec ep_mat
  |> ExpPolynomial.Vector.add_term
       (ExpPolynomial.scalar (Vec.coeff Linear.const_dim linterm))
       Linear.const_dim

let mp srk tf =
  let tf = TF.linearize srk tf in
  match Smt.is_sat srk (TF.formula tf) with
  | `Unknown -> failwith "SMT solver should not return unknown for QRA formulas"
  | `Unsat -> (logf ~attributes:[`Bold; `Green] "Transition formula UNSAT, done"); mk_false srk
  | `Sat ->
     let qdlts_abs =
       DLTSPeriodicRational.abstract_rational srk tf
       |> DLTS.simplify srk ~scale:true
     in
     let module PLM = Lts.PartialLinearMap in
     let omega_domain = snd (PLM.iteration_sequence qdlts_abs.dlts) in
     let dim = BatArray.length qdlts_abs.simulation in
     (* Columns of G form a basis for omega domain. *)
     let g =
       constraints_to_generators dim (Linear.QQMatrix.of_rows omega_domain)
     in
     let tr = PLM.map qdlts_abs.dlts in
     let tr_omega = inv_subspace_restriction tr g in
     (* Columns of Z form basis for integer domain of tr_omega. *)
     let z = int_eigenspace (Linear.QQMatrix.nb_columns g) tr_omega in
     let gz = Linear.QQMatrix.mul g z in
     let tr_z = inv_subspace_restriction tr gz in
     (* Introduce one symbol per dimension of the integer domain. *)
     let gz_symbols =
       Array.init
         (Linear.QQMatrix.nb_columns gz)
         (fun i -> mk_symbol srk ~name:(Format.asprintf "dta<%d>" i) `TyInt)
     in
     (* GZz = Sx *)
     let sim_constraints =
       BatList.init
         (Array.length qdlts_abs.simulation)
         (fun i ->
           let gz_term =
             Linear.QQMatrix.row i gz
             |> Linear.term_of_vec srk (fun j -> (mk_const srk gz_symbols.(j)))
           in
           mk_eq srk qdlts_abs.simulation.(i) gz_term)
     in
     let gz_symbols_set = Symbol.Set.of_array gz_symbols in
     (* exists x,x'. F(x,x') /\ GZz = Sx *)
     let guard =
       mk_and srk (TF.formula tf::sim_constraints)
       |> Quantifier.mbp srk (fun s -> Symbol.Set.mem s gz_symbols_set)
       |> SrkSimplify.simplify_dda srk
       |> SrkSimplify.eliminate_floor srk
     in
     let tr_z_exp = BatOption.get (ExpPolynomial.exponentiate_rational tr_z) in
     let term_of_dim i =
       if i == Linear.const_dim then mk_one srk
       else mk_const srk gz_symbols.(i)
     in
     let algebra = function 
       | `Tru -> Periodic.make [mk_true srk]
       | `Fls -> Periodic.make [mk_false srk]
       | `And xs -> Periodic.mapn (mk_and srk) xs
       | `Or xs -> Periodic.mapn (mk_or srk) xs
       | `Not x -> Periodic.map (mk_not srk) x
       | `Atom (`Arith (op, s, t)) -> 
          begin
            match SrkSimplify.simplify_integer_atom srk op s t with 
            | `CompareZero (op, vec) ->
               let cf = closed_form gz_symbols (Vec.negate vec) tr_z_exp in
               let predicate = match op with
                 | `Eq -> `Zero
                 | `Leq -> `Nonneg
                 | `Lt -> `Pos
               in
               XSeq.seq_of_compare_atom srk predicate cf term_of_dim
            | `Divides (divisor, vec) ->
               XSeq.seq_of_divides_atom srk divisor (closed_form gz_symbols vec tr_z_exp) term_of_dim
            | `NotDivides (divisor, vec) ->
               XSeq.seq_of_divides_atom srk divisor (closed_form gz_symbols vec tr_z_exp) term_of_dim
               |> Periodic.map (mk_not srk)
          end
       | `Quantify _ -> failwith "should not see quantifiers in the TF"
       | `Atom (`ArrEq _) -> failwith "should not see ArrEq in the TF"
       | `Proposition _ -> failwith "should not see proposition in the TF"
       | `Ite _ -> failwith "should not see ite in the TF"
     in
     let xseq = Formula.eval srk algebra guard in
     mk_and srk (sim_constraints@(Periodic.period xseq))
     |> Quantifier.mbp srk (fun s -> not (Symbol.Set.mem s gz_symbols_set))
     |> mk_not srk

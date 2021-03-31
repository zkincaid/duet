open Syntax
open BatPervasives

include Log.Make(struct let name = "Srk.SolvablePolynomial" end)

module V = Linear.QQVector
module QQMatrix = Linear.QQMatrix

module IntSet = SrkUtil.Int.Set
module IntMap = SrkUtil.Int.Map
module DArray = BatDynArray

module QQX = Polynomial.QQX
module QQXs = Polynomial.QQXs
module Monomial = Polynomial.Monomial
module CS = CoordinateSystem

module UP = ExpPolynomial.UltPeriodic

module PLM = Lts.PartialLinearMap

module TF = TransitionFormula

(* Closed forms for solvable polynomial maps with periodic rational
   eigenvalues: multi-variate polynomials with ultimately periodic
   exponential polynomial coefficients *)
module UPXs = struct
  include Polynomial.MakeMultivariate(UP)
  module MonomialSet = Set.Make(Monomial)

  let eval upxs k =
    BatEnum.fold (fun e (up, m) ->
        QQXs.add_term (UP.eval up k) m e)
      QQXs.zero
      (enum upxs)

  let map_coeff f upxs =
    BatEnum.fold (fun e (up, m) ->
        add_term (f m up) m e)
      zero
      (enum upxs)

  let flatten period =
    let monomials =
      List.fold_left (fun set upxs ->
          BatEnum.fold (fun set (_, m) ->
              MonomialSet.add m set)
            set
            (enum upxs))
        MonomialSet.empty
        period
    in
    MonomialSet.fold (fun m upxs ->
        let up =
          List.map (coeff m) period
          |> UP.flatten
        in
        add_term up m upxs)
      monomials
      zero
end

type block =
  { blk_transform : QQ.t array array;
    blk_add : QQXs.t array }

(* A solvable polynomial map is a list of blocks representing a function
   x_1' = A_1*x_1 + p_1()
   x_2' = A_2*x_2 + p_2(x_1)
   ...
   x_m' = A_m*x_m + p_m(x_1,...,x_{m-1})

   where each A_i is a rational matrix and each p_i is a vector of
   polynomials over the variables of lower blocks. *)
type solvable_polynomial = block list

(* Map Q^n -> Q^n defined by an array of polynomials
     p_0(x_0,...,x_{n-1})
     ...
     p_{n-1}(x_0,...,x_{n-1}) *)
type polynomial_map = QQXs.t array

(* Matrix-polynomial vector multiplication.  Assumes that the columns of m are
   a subset of {0,...,|polyvec|-1}. *)
let matrix_polyvec_mul m polyvec =
  Array.init (QQMatrix.nb_rows m) (fun i ->
      BatEnum.fold (fun p (coeff, j) ->
          QQXs.add p (QQXs.scalar_mul coeff polyvec.(j)))
        QQXs.zero
        (V.enum (QQMatrix.row i m)))

let vec_upxsvec_dot vec1 vec2 =
  BatEnum.fold (fun ep i ->
      UPXs.add
        ep
        (UPXs.scalar_mul (UP.scalar (V.coeff i vec1)) vec2.(i)))
    UPXs.zero
    (0 -- (Array.length vec2 - 1))

let vec_qqxsvec_dot vec1 vec2 =
  BatEnum.fold (fun ep i ->
      QQXs.add
        ep
        (QQXs.scalar_mul (V.coeff i vec1) vec2.(i)))
    QQXs.zero
    (0 -- (Array.length vec2 - 1))

let term_of_ocrs srk loop_counter pre_term_of_id post_term_of_id =
  let open OCRS in
  let open Type_def in
  let ss_pre = SSVar "k" in
  let rec go = function
    | Plus (x, y) -> mk_add srk [go x; go y]
    | Minus (x, y) -> mk_sub srk (go x) (go y)
    | Times (x, y) -> mk_mul srk [go x; go y]
    | Divide (x, y) -> mk_div srk (go x) (go y)
    | Product xs -> mk_mul srk (List.map go xs)
    | Sum xs -> mk_add srk (List.map go xs)
    | Symbolic_Constant name -> pre_term_of_id name
    | Base_case (name, index) ->
      assert (index = 0);
      pre_term_of_id name
    | Input_variable name ->
      assert (name = "k");
      loop_counter
    | Output_variable (name, subscript) ->
      assert (subscript = ss_pre);
      post_term_of_id name
    | Rational k -> mk_real srk (Mpqf.of_mpq k)
    | Undefined -> assert false
    | Pow (x, y) -> Nonlinear.mk_pow srk (go x) (go y)
    | Log (base, x) ->
      Nonlinear.mk_log srk (mk_real srk (Mpqf.of_mpq base)) (go x)
    | IDivide (x, y) ->
      mk_idiv srk (go x) (mk_real srk (Mpqf.of_mpq y))
    | Mod (x, y) ->
      mk_mod srk (go x) (go y)
    | Iif (func, ss) ->
      let arg =
        match ss with
        | SSVar "k" -> loop_counter
        | SAdd ("k", i) ->
          mk_add srk [loop_counter; mk_real srk (QQ.of_int i)]
        | _ -> assert false
      in
      let sym =
        if not (is_registered_name srk func) then
          register_named_symbol srk func (`TyFun ([`TyReal], `TyReal));
        get_named_symbol srk func
      in
      mk_app srk sym [arg]
    | Binomial (_, _) | Factorial _ | Sin _ | Cos _ | Arctan _ | Pi | Shift (_, _) ->
      assert false
  in
  go

let block_size block = Array.length block.blk_add

let dimension sp =
  List.fold_left (+) 0 (List.map block_size sp)

let iter_blocks f sp =
  List.fold_left (fun offset block ->
      f offset block;
      (offset + (block_size block)))
    0
    sp
  |> ignore

(* Flatten a block representation of a solvable polynomial map, into a polynomial map *)
let to_polynomial_map (sp : solvable_polynomial) =
  let pm = DArray.create () in
  sp |> iter_blocks (fun offset block ->
      BatEnum.iter (fun i ->
          let rhs =
            BatArray.fold_lefti
              (fun p j coeff ->
                 QQXs.add_term coeff (Monomial.singleton (offset + j) 1) p)
              block.blk_add.(i)
              block.blk_transform.(i)
          in
          DArray.add pm rhs)
        (0 -- (block_size block - 1)));
  DArray.to_array pm

module MonomialSet = BatSet.Make(Monomial)
module MonomialMap = BatMap.Make(Monomial)

(* Given solvable polynomial map and a set of monomials, compute a set
   of monomials that contains the given set and such that the subspace
   of polynomials by the monomials is invariant under the polynomial
   map.  monomial_closure is guaranteed to terminate only when the
   given polynomial map is solvable. *)
let monomial_closure (pm : polynomial_map) (monomials : MonomialSet.t) =
  let rhs = QQXs.substitute (fun i -> pm.(i)) in
  let rec fix worklist monomials =
    match worklist with
    | [] -> monomials
    | (w::worklist) ->
      let (worklist, monomials) =
        BatEnum.fold
          (fun (worklist, monomials) (_, m) ->
             if MonomialSet.mem m monomials then
               (worklist, monomials)
             else
               (m::worklist, MonomialSet.add m monomials))
          (worklist, monomials)
          (QQXs.enum (rhs (QQXs.add_term QQ.one w QQXs.zero)))
      in
      fix worklist monomials
  in
  fix (MonomialSet.elements monomials) monomials

(* Given a solvable polynomial map restricted to an algebraic variety,
   compute a DLTS that simulates it via a polynomial map *)
let dlts_of_solvable_algebraic (pm : polynomial_map) (ideal : QQXs.t list) =
  (* least set of monomials that (1) contains all degree-1 monmials
     (2) every polynomial in ideal can be wrriten as linear
     combination of monomials in the set and (3) is invariant under
     the given polyomial map *)
  let monomials =
    let dim_monomials =
      BatEnum.fold (fun monomials i ->
          MonomialSet.add (Monomial.singleton i 1) monomials)
        MonomialSet.empty
        (0 -- (Array.length pm - 1))
    in
    List.fold_left (fun monomials p ->
        BatEnum.fold
          (fun monomials (_, m) -> MonomialSet.add m monomials)
          monomials
          (QQXs.enum p))
      dim_monomials
      ideal
    |> monomial_closure pm
  in
  let rhs m = QQXs.substitute (fun i -> pm.(i)) (QQXs.add_term QQ.one m QQXs.zero) in
  let simulation = Array.of_list (MonomialSet.elements monomials) in
  let rev_simulation =
    BatArray.fold_lefti (fun rev_sim i m ->
        MonomialMap.add m i rev_sim)
      MonomialMap.empty
      simulation
  in
  let vec_of_polynomial p =
    QQXs.enum p
    /@ (fun (coeff, m) -> (coeff, MonomialMap.find m rev_simulation))
    |> V.of_enum
  in
  let guard = List.map vec_of_polynomial ideal in
  let map =
    BatArray.fold_lefti (fun map i m ->
        QQMatrix.add_row i (vec_of_polynomial (rhs m)) map)
      QQMatrix.zero
      simulation
  in
  (PLM.make map guard, simulation)

let pp_dim formatter i =
  let rec to_string i =
    if i < 26 then
        Char.escaped (Char.chr (97 + i))
    else
      (to_string (i/26)) ^ (Char.escaped (Char.chr (97 + (i mod 26))))
  in
  Format.pp_print_string formatter (to_string i)

let _pp_block formatter block =
  let open Format in
  let size = block_size block in
  fprintf formatter "@[<v 0>";
  for i = 0 to (size - 1) do
    if i = size / 2 then
      fprintf formatter "|%a'| = |@[<h 1>" pp_dim i
    else
      fprintf formatter "|%a'|   |@[<h 1>" pp_dim i;
    for j = 0 to (size - 1) do
      fprintf formatter "%a@;" QQ.pp block.blk_transform.(i).(j)
    done;
    if i = size / 2 then
      fprintf formatter "| |%a| + |%a|@]@;" pp_dim i (QQXs.pp pp_dim) block.blk_add.(i)
    else
      fprintf formatter "| |%a|   |%a|@]@;"
        pp_dim i
        (QQXs.pp pp_dim) block.blk_add.(i)
  done;
  fprintf formatter "@]"

(* Compute closed-form representation of the dynamics of solvable
   polynomial map using OCRS *)
let closure_ocrs sp =
  let open OCRS in
  let open Type_def in

  (* pre/post subscripts *)
  let ss_pre = SSVar "k" in
  let ss_post = SAdd ("k", 1) in

  (* Map identifiers to their closed forms, so that they can be used
     in the additive term of blocks at higher strata *)
  let cf =
    Array.make (dimension sp) (Rational (Mpqf.to_mpq QQ.zero))
  in
  let close_block block offset =
    let size = Array.length block.blk_add in
    if size = 0 then
      []
    else
      let dim_vec = Array.init size (fun i -> string_of_int (offset + i)) in
      let ocrs_transform =
        Array.map (Array.map Mpqf.to_mpq) block.blk_transform
      in
      let ocrs_add =
        Array.init size (fun i ->
            let cf_monomial m =
              Monomial.enum m
              /@ (fun (id, pow) -> Pow (cf.(id), Rational (Mpq.of_int pow)))
              |> BatList.of_enum
            in
            QQXs.enum block.blk_add.(i)
            /@ (fun (coeff, m) ->
                Product (Rational (Mpqf.to_mpq coeff)::(cf_monomial m)))
            |> (fun x -> Sum (BatList.of_enum x)))
      in
      let block_closed =
        let mat_rec =
          VEquals (Ovec (dim_vec, ss_post),
                   ocrs_transform,
                   Ovec (dim_vec, ss_pre),
                   ocrs_add)
        in
        logf "Block:@\n%s" (Mat_helpers.matrix_rec_to_string mat_rec);
        Log.time "OCRS" (Ocrs.solve_mat_recurrence mat_rec) false
      in
      block_closed
  in
  sp |> iter_blocks (fun offset block ->
      close_block block offset
      |> List.iteri (fun i ineq ->
          match ineq with
          | Equals (_, y) -> cf.(offset + i) <- y
          | _ -> assert false));
  cf

(* Given a matrix in which each vector in the standard basis is a
   periodic generalized eigenvector, find a PRSD over the standard
   basis. *)
let standard_basis_prsd mA size =
  let dims = BatList.of_enum (0 -- (size - 1)) in
  let new_prsd =
    List.rev (Linear.periodic_rational_spectral_decomposition mA dims)
  in
  let id = QQMatrix.identity dims in
  let get_period_eigenvalue v =
    let (p, lambda, _) =
      BatList.find (fun (p, lambda, _) ->
          V.is_zero
            (Linear.vector_left_mul v
               (QQMatrix.exp
                  (QQMatrix.add
                     (QQMatrix.exp mA p)
                     (QQMatrix.scalar_mul (QQ.negate lambda) id))
                  size)))
        new_prsd
    in
    (p, lambda)
  in
  (0 -- (size - 1))
  /@ (fun i ->
      let v = V.of_term QQ.one i in
      let (p, lambda) = get_period_eigenvalue v in
      (p, lambda, v))
  |> BatList.of_enum

(* Compute closed-form representation of the dynamics of solvable
   polynomial map with periodic rational eigenvalues *)
let closure_periodic_rational sp =
  (* Map identifiers to their closed forms, so that they can be used
     in the additive term of blocks at higher strata *)
  let cf =
    Array.make (dimension sp) UPXs.zero
  in
  (* Substitute closed forms in for a polynomial *)
  let substitute_closed_forms p =
    BatEnum.fold (fun up (coeff, m) ->
        BatEnum.fold (fun m_up (i, pow) ->
            UPXs.mul m_up (UPXs.exp cf.(i) pow))
          (UPXs.scalar (UP.make [] [ExpPolynomial.scalar coeff]))
          (Monomial.enum m)
        |> UPXs.add up)
      UPXs.zero
      (QQXs.enum p)
  in
  sp |> iter_blocks (fun offset block ->
      let transform = QQMatrix.of_dense block.blk_transform in
      let size = block_size block in
      let add =
        Array.init size (fun i ->
            substitute_closed_forms block.blk_add.(i))
      in
      let prsd =
        try standard_basis_prsd transform size
        with Not_found -> assert false
      in
      prsd |> BatList.iteri (fun i (p, lambda, v) ->

          (* v is a generalized eigenvector of transform^p.  Traverse the
             Jordan chain generated by v from the bottom up, computing
             closed forms along the way. *)
          let jordan_chain =
            Linear.jordan_chain (QQMatrix.exp transform p) lambda v
          in
          let cf_i =
            if QQ.equal lambda QQ.zero then begin
              assert (p == 1);
              BatList.fold_right (fun v cf ->
                  let cf_transform =
                    BatEnum.fold (fun v_cf (coeff, i) ->
                        UPXs.add_term
                          (UP.make [coeff] [ExpPolynomial.zero])
                          (Monomial.singleton (offset + i) 1)
                          v_cf)
                      UPXs.zero
                      (V.enum v)
                  in
                  let cf_add =
                    UPXs.map_coeff
                      (fun _ -> UP.shift [QQ.zero])
                      (UPXs.add cf (vec_upxsvec_dot v add))
                  in
                  UPXs.add cf_transform cf_add)
                jordan_chain
                UPXs.zero
            end else begin
              List.fold_right (fun v cf ->
                  let cf_transform =
                    let v_Ai = (* vA^0, ..., vA^{p-1} *)
                      BatEnum.fold (fun (v_transform, xs) _ ->
                          let next = Linear.vector_left_mul v_transform transform in
                          (next, next::xs))
                        (v, [v])
                        (1 -- (p - 1))
                      |> snd
                      |> List.rev
                    in
                    BatEnum.fold (fun cf_A i ->
                        let period =
                          List.map (fun r ->
                              ExpPolynomial.of_term (QQX.scalar (V.coeff i r)) lambda)
                            v_Ai
                        in
                        let up = UP.make [] period in
                        UPXs.add_term
                          up
                          (Monomial.singleton (offset + i) 1)
                          cf_A)
                      UPXs.zero
                      (0 -- (size - 1))
                  in

                  let cf_add =
                    (0 -- (p - 1)) |> BatEnum.map (fun i ->
                        (* sum_{j=0}^{p-1} v * A^{p-j-1} * cf_add(pk+j+i) *)
                        let sum_pk_i =
                          BatEnum.fold (fun sum j ->
                              UPXs.add
                                sum
                                (vec_upxsvec_dot
                                   (Linear.vector_left_mul
                                      v
                                      (QQMatrix.exp transform (p-j-1)))
                                   (Array.map
                                      (UPXs.map_coeff (fun _ f ->
                                           UP.compose_left_affine f p (j+i)))
                                      add)))
                            UPXs.zero
                            (0 -- (p - 1))
                        in
                        let cf_pk_i = (* cf(pk+i) *)
                          UPXs.map_coeff (fun _ f ->
                              UP.compose_left_affine f p i)
                            cf
                        in
                        (* sum_{j=0}^{i-1} v * A^{i-j-1} * cf_add(j) *)
                        let initial =
                          BatEnum.fold (fun sum j ->
                              let cf_add_j =
                                Array.map (fun f -> UPXs.eval f j) add
                              in
                              let vAij =
                                Linear.vector_left_mul
                                  v
                                  (QQMatrix.exp transform (i-j-1))
                              in
                              QQXs.add sum (vec_qqxsvec_dot vAij cf_add_j))
                            QQXs.zero
                            (0 -- (i-1))
                        in
                        let get_initial m = QQXs.coeff m initial in
                        UPXs.map_coeff
                          (fun m f -> UP.solve_rec ~initial:(get_initial m) lambda f)
                          (UPXs.add cf_pk_i sum_pk_i))
                    |> BatList.of_enum
                    |> UPXs.flatten
                  in
                  UPXs.add cf_transform cf_add)
                jordan_chain
                UPXs.zero
            end
          in
          cf.(offset + i) <- cf_i));
  cf

(** Solvable polynomial abstractions ****************************************************)
(* map pre-state coordinates to their post-state counterparts *)
let post_coord_map cs tr_symbols =
  List.fold_left
    (fun map (sym, sym') ->
       try
         let coord = CS.cs_term_id cs (`App (sym, [])) in
         let coord' = CS.cs_term_id cs (`App (sym', [])) in
         IntMap.add coord coord' map
       with Not_found -> map)
    IntMap.empty
    tr_symbols

(* Are most coefficients of a vector negative? *)
let is_vector_negative vec =
  let sign =
    BatEnum.fold (fun sign (coeff,_) ->
        if QQ.lt coeff QQ.zero then
          sign - 1
        else
          sign + 1)
      0
      (V.enum vec)
  in
  sign < 0

exception IllFormedRecurrence

(* Write the affine hull of a wedge as Ax' = Bx + c, where c is vector of
   polynomials in recurrence terms, and the non-zero rows of A are linearly
   independent. *)
let rec_affine_hull srk wedge tr_symbols rec_terms rec_ideal =
  let cs = Wedge.coordinate_system wedge in

  (* pre_dims is a set of dimensions corresponding to pre-state
     dimensions. pre_map is a mapping from dimensions that correspond to
     post-state dimensions to their pre-state counterparts *)
  let (pre_map, pre_dims) =
    List.fold_left (fun (pre_map, pre_dims) (s,s') ->
        let id_of_sym sym =
          try
            CS.cs_term_id cs (`App (sym, []))
          with Not_found ->
            assert false
        in
        let pre = id_of_sym s in
        let post = id_of_sym s' in
        (IntMap.add post pre pre_map, IntSet.add pre pre_dims))
      (IntMap.empty, IntSet.empty)
      tr_symbols
  in

  (* An additive dimension is one that is allowed to appear as an additive
     term *)
  let cs_dim = CS.dim cs in
  let additive_dim x = x >= cs_dim in
  let post_dim x = IntMap.mem x pre_map in
  let pp_coord formatter i =
    if i < cs_dim then
      Format.fprintf formatter "w[%a]"
        (Term.pp srk) (CS.term_of_coordinate cs i)
    else
      Format.fprintf formatter "v[%a]"
        (Term.pp srk) (DArray.get rec_terms (i - cs_dim))
  in
  let rec_term_rewrite =
    let ideal = ref rec_ideal in
    let elim_order =
      Monomial.block [not % additive_dim] Monomial.degrevlex
    in
    rec_terms |> DArray.iteri (fun i t ->
        let vec = CS.vec_of_term cs t in
        let p =
          QQXs.add_term
            (QQ.of_int (-1))
            (Monomial.singleton (i + cs_dim) 1)
            (QQXs.of_vec ~const:(CS.const_id) vec)
        in
        ideal := p::(!ideal));
    Polynomial.Rewrite.mk_rewrite elim_order (!ideal)
    |> Polynomial.Rewrite.grobner_basis
  in
  let basis =
    let elim_order =
      Monomial.block [not % additive_dim; not % post_dim] Monomial.degrevlex
    in
    BatList.filter_map
      (fun x ->
         let x' = Polynomial.Rewrite.reduce rec_term_rewrite x in
         if QQXs.equal x' QQXs.zero then
           None
         else
           Some x')
      (Wedge.vanishing_ideal wedge)
    |> Polynomial.Rewrite.mk_rewrite elim_order
    |> Polynomial.Rewrite.grobner_basis
    |> Polynomial.Rewrite.generators
  in
  let (mA, mB, pvc, _) =
    logf ~attributes:[`Bold] "Vanishing ideal:";
    List.fold_left (fun (mA,mB,pvc,i) p ->
        try
          logf "  @[%a@]" (QQXs.pp pp_coord) p;
          let (vecA, vecB, pc) =
            BatEnum.fold (fun (vecA, vecB, pc) (coeff, monomial) ->
                match BatList.of_enum (Monomial.enum monomial) with
                | [(dim, 1)] when IntMap.mem dim pre_map ->
                  (V.add_term (QQ.negate coeff) (IntMap.find dim pre_map) vecA,
                   vecB,
                   pc)
                | [(dim, 1)] when IntSet.mem dim pre_dims ->
                  (vecA, V.add_term coeff dim vecB, pc)
                | monomial_list ->
                  if List.for_all (additive_dim % fst) monomial_list then
                    (vecA, vecB, QQXs.add_term coeff monomial pc)
                  else
                    raise IllFormedRecurrence)
              (V.zero, V.zero, QQXs.zero)
              (QQXs.enum p)
          in
          let (vecA, vecB, pc) =
            if is_vector_negative vecA then
              (V.negate vecA, V.negate vecB, QQXs.negate pc)
            else
              (vecA, vecB, pc)
          in
          let pc =
            QQXs.substitute (fun i ->
                QQXs.add_term
                  QQ.one
                  (Monomial.singleton (i - cs_dim) 1)
                  QQXs.zero)
              pc
          in
          let mAt = QQMatrix.transpose mA in
          match Linear.solve mAt vecA with
          | Some r ->
            (* vecA is already in the span of mA -- r*mA = vecA. *)
            let vecB = V.sub vecB (Linear.vector_left_mul r mB) in
            if V.is_zero vecB then
              (mA, mB, pvc, i)
            else
              let pc =
                let rpc = (* r*pvc *)
                  BatEnum.fold (fun p (coeff, i) ->
                      QQXs.add p (QQXs.scalar_mul coeff (List.nth pvc i)))
                    QQXs.zero
                    (V.enum r)
                in
                QQXs.sub pc rpc
              in
              (mA,
               QQMatrix.add_row i vecB mB,
               pc::pvc,
               i+1)
          | None ->
            (QQMatrix.add_row i vecA mA,
             QQMatrix.add_row i vecB mB,
             pc::pvc,
             i+1)
        with IllFormedRecurrence -> (mA, mB, pvc, i))
      (QQMatrix.zero, QQMatrix.zero, [], 0)
      basis
  in
  (mA, mB, List.rev pvc)

(* Given a wedge w, compute A,B,C such that w |= Ax' = BAx + Cy, and such that
   the row space of A is maximal. *)
let extract_affine_transformation srk wedge tr_symbols rec_terms rec_ideal =
  let (mA, mB, pvc) = rec_affine_hull srk wedge tr_symbols rec_terms rec_ideal in
  let (dlts, mT) = Lts.determinize (mA, mB) in
  let mS =
    let mD = QQMatrix.mul (PLM.map dlts) mT in
    match Lts.containment_witness (mA,mB) (mT,mD) with
    | Some k -> k
    | None -> assert false
  in
  let mA = mT in
  let mB = PLM.map dlts in
  let pvc = matrix_polyvec_mul mS (Array.of_list pvc) in
  logf ~attributes:[`Blue] "Affine transformation:";
  logf " A: @[%a@]" QQMatrix.pp mA;
  logf " B: @[%a@]" QQMatrix.pp mB;
  (mA, mB, pvc)

(* Iteration domain element.  Recurrence equations have the form
     A_1 * x' = B_1 * A_1 * x + c_1
     ...
     A_n * x' = B_n * A_n * x + c_n

   where each A_i/B_i is a rational matrix and each c_i is a vector of
   polynomial over dimensions corresponding to constant terms and the rows
   of A_1 ... A_{i-1}.

   The list of B_i/c_i's is stored in rec_eq.  The list of A_is is stored
   implicitly in term_of_id, which associates integer identifiers with
   linear term (so term_of_id.(nb_constants) corresponds to the first row of
   A_1, term_of_id.(nb_constants+size(A_1)) corresponds to the first row of
   A_2, ...).  Similarly for inequations in rec_leq. *)
type 'a t =
  { term_of_id : ('a term) array;
    nb_constants : int;
    block_eq : block list;
    block_leq : block list }

let nb_equations iter =
  List.fold_left (+) 0 (List.map block_size iter.block_eq)

let pp srk tr_symbols formatter iter =
  let post_map = TF.post_map srk tr_symbols in
  let postify =
    let subst sym =
      if Symbol.Map.mem sym post_map then
        Symbol.Map.find sym post_map
      else
        mk_const srk sym
    in
    substitute_const srk subst
  in
  let pp_id formatter id =
    Term.pp srk formatter iter.term_of_id.(id)
  in
  let pp_rec cmp offset formatter recurrence =
    recurrence.blk_transform |> Array.iteri (fun i row ->
        let nonzero = ref false in
        Format.fprintf formatter "(%a) %s @[<hov 1>"
          (Term.pp srk) (postify iter.term_of_id.(offset + i))
          cmp;
        row |> Array.iteri (fun j coeff ->
            if not (QQ.equal coeff QQ.zero) then begin
              if !nonzero then
                Format.fprintf formatter "@ + "
              else
                nonzero := true;
              Format.fprintf formatter "(%a)*(%a)"
                QQ.pp coeff
                (Term.pp srk) (iter.term_of_id.(offset + j))
            end
          );
        if !nonzero then
          Format.fprintf formatter "@ + ";
        Format.fprintf formatter "%a@]@;"
          (QQXs.pp pp_id) recurrence.blk_add.(i))
  in
  let offset =
    List.fold_left (fun offset recurrence ->
        pp_rec "=" offset formatter recurrence;
        (Array.length recurrence.blk_transform + offset))
      iter.nb_constants
      iter.block_eq
  in
  ignore (List.fold_left (fun offset recurrence ->
      pp_rec "<=" offset formatter recurrence;
      (Array.length recurrence.blk_transform + offset))
      offset
      iter.block_leq)

exception Not_a_polynomial

(* A block corresponds to a set of polynomial equations.  block_zeros
   produces a list of these equations, represented in the coordinate
   system term_of_id.  Adds terms to term_of_id as necessary -- one
   per dimension of the block. *)
let block_zeros cs block simulation tr_symbols term_of_id =
  let post_coord_map = post_coord_map cs tr_symbols in
  let size = Array.length block.blk_add in
  let offset = DArray.length term_of_id in

  for i = 0 to size - 1 do
    DArray.add term_of_id (CS.term_of_vec cs (QQMatrix.row i simulation))
  done;

  (0 -- (size - 1)) /@ (fun i ->
      let lhs =
        QQXs.of_vec ~const:CS.const_id (QQMatrix.row i simulation)
        |> QQXs.substitute (fun coord ->
            assert (IntMap.mem coord post_coord_map);
            QQXs.of_dim (IntMap.find coord post_coord_map))
      in
      let add =
        QQXs.substitute (fun i ->
            (CS.polynomial_of_term cs (DArray.get term_of_id i)))
          block.blk_add.(i)
      in
      let rhs =
        BatArray.fold_lefti (fun p j coeff ->
            QQXs.add p
              (QQXs.scalar_mul coeff
                 (CS.polynomial_of_term cs
                    (DArray.get term_of_id (offset + j)))))
          QQXs.zero
          block.blk_transform.(i)
        |> QQXs.add add
      in
      QQXs.add lhs (QQXs.negate rhs))
  |> BatList.of_enum

let extract_solvable_polynomial_eq srk wedge tr_symbols term_of_id =
  let cs = Wedge.coordinate_system wedge in

  let rec fix rec_ideal =
    logf "New stratum (%d terms)" (DArray.length term_of_id);
    let (mA,mB,blk_add) =
      extract_affine_transformation srk wedge tr_symbols term_of_id rec_ideal
    in
    let size = Array.length blk_add in
    if size = 0 then
      []
    else
      let blk_transform = QQMatrix.dense_of mB size size in
      let block = { blk_transform; blk_add } in
      let zeros = block_zeros cs block mA tr_symbols term_of_id in
      block::(fix (zeros@rec_ideal))
  in
  fix []

(* Extract a stratified system of matrix recurrences *)
let extract_periodic_rational_matrix_eq srk wedge tr_symbols term_of_id =
  let cs = Wedge.coordinate_system wedge in

  (* Detect stratified recurrences *)
  let rec fix rec_ideal =
    logf "New stratum (%d recurrence terms)" (DArray.length term_of_id);
    let (mA,mB,blk_add) =
      extract_affine_transformation srk wedge tr_symbols term_of_id rec_ideal
    in

    let dims = SrkUtil.Int.Set.elements (QQMatrix.row_set mA) in
    let prsd = Linear.periodic_rational_spectral_decomposition mB dims in
    let mU =
      BatList.fold_lefti (fun m i (_,_,v) ->
          QQMatrix.add_row i v m)
        QQMatrix.zero
        prsd
    in

    let mUA = QQMatrix.mul mU mA in
    let mUB = QQMatrix.mul mU mB in
    let mB = match Linear.divide_right mUB mU with
      | Some x -> x
      | None -> assert false
    in
    let mA = mUA in
    let blk_add = matrix_polyvec_mul mU blk_add in

    let size = Array.length blk_add in
    if size = 0 then
      []
    else
      let blk_transform = QQMatrix.dense_of mB size size in
      let block = { blk_transform; blk_add } in
      let zeros = block_zeros cs block mA tr_symbols term_of_id in
      block::(fix (zeros@rec_ideal))
  in
  fix []

(* Extract recurrences of the form t' <= base * t + p, where p is a
   polynomial over recurrence terms *)
let extract_vector_leq srk wedge tr_symbols term_of_id base =
  (* For each transition symbol (x,x'), allocate a symbol delta_x,
     which is constrained to be equal to x'-base*x.  For each recurrence
     term t, allocate a symbol add_t, which is constrained to be equal
     to (the pre-state value of) t.  After projecting out all
     variables *except* the delta and add variables, we have a wedge
     where each constraint corresponds to a recurrence inequation. *)
  let delta =
    List.map (fun (s,_) ->
        let name = "delta[" ^ (show_symbol srk s) ^ "," ^ (QQ.show base) ^ "]" in
        let typ =
          if typ_symbol srk s == `TyInt && (QQ.to_zz base != None) then
            `TyInt
          else
            `TyReal
        in
        mk_symbol srk ~name typ)
      tr_symbols
  in
  let add =
    DArray.map (fun t ->
        let name = "a[" ^ (Term.show srk t) ^ "]" in
        mk_symbol srk ~name (term_typ srk t :> typ))
      term_of_id
  in
  let delta_map =
    List.fold_left2 (fun map delta (s,_) ->
        Symbol.Map.add delta (mk_const srk s) map)
      Symbol.Map.empty
      delta
      tr_symbols
  in
  let add_map =
    BatEnum.fold
      (fun map i ->
         Symbol.Map.add (DArray.get add i) (QQXs.of_dim i) map)
      Symbol.Map.empty
      (0 -- (DArray.length add - 1))
  in
  let add_symbols =
    DArray.fold_right Symbol.Set.add add Symbol.Set.empty
  in
  let diff_symbols =
    List.fold_right Symbol.Set.add delta add_symbols
  in
  let constraints =
    let base_term = mk_real srk base in
    (List.map2 (fun delta (s,s') ->
         mk_eq srk
           (mk_const srk delta)
           (mk_sub srk (mk_const srk s') (mk_mul srk [base_term; mk_const srk s])))
        delta
        tr_symbols)
    @ (BatEnum.map
         (fun i ->
            mk_eq srk
              (mk_const srk (DArray.get add i))
              (DArray.get term_of_id i))
         (0 -- ((DArray.length add) - 1))
       |> BatList.of_enum)
    @ (Wedge.to_atoms wedge)
  in
  (* Wedge over delta and add variables *)
  let diff_wedge =
    let subterm x = Symbol.Set.mem x add_symbols in
    Wedge.of_atoms srk constraints
    |> Wedge.exists ~subterm (fun x -> Symbol.Set.mem x diff_symbols)
  in
  let diff_cs = Wedge.coordinate_system diff_wedge in
  let base_transform = [|[|base|]|] in
  let recurrences = ref [] in
  let add_recurrence = function
    | (`Eq, _) ->
      (* Skip equations -- we assume that all recurrence equations have
         already been extracted. *)
      ()
    | (`Geq, t) ->
      (* Rewrite t>=0 as (rec_term'-rec_term) <= blk_add, where rec_term is a
         linear term and blk_add is a polynomial over recurrence terms of
         lower strata. *)
      let (c, t) = V.pivot Linear.const_dim t in
      let (rec_term, blk_add) =
        BatEnum.fold
          (fun (rec_term, blk_add) (coeff, coord) ->
             let diff_term = CS.term_of_coordinate diff_cs coord in
             match Term.destruct srk diff_term with
             | `App (sym, []) when Symbol.Map.mem sym delta_map ->
               let term =
                 mk_mul srk [mk_real srk (QQ.negate coeff);
                             Symbol.Map.find sym delta_map]
               in
               (term::rec_term, blk_add)
             | _ ->
               let to_mvp = function
                 | `App (sym, []) ->
                   (try Symbol.Map.find sym add_map
                    with Not_found -> assert false)
                 | `Real k -> QQXs.scalar k
                 | `Add xs -> List.fold_left QQXs.add QQXs.zero xs
                 | `Mul xs -> List.fold_left QQXs.mul QQXs.one xs
                 | _ -> raise Not_a_polynomial
               in
               let term =
                 QQXs.scalar_mul coeff (Term.eval srk to_mvp diff_term)
               in
               (rec_term, QQXs.add term blk_add))
          ([], QQXs.scalar c)
          (V.enum t)
      in
      if rec_term != [] then
        let recurrence =
          { blk_transform = base_transform;
            blk_add = [|blk_add|] }
        in
        recurrences := recurrence::(!recurrences);
        DArray.add term_of_id (mk_add srk rec_term);
  in
  let add_recurrence x =
    try add_recurrence x
    with Not_a_polynomial -> ()
  in
  List.iter add_recurrence (Wedge.polyhedron diff_wedge);
  List.rev (!recurrences)

(* Extract a system of recurrencs of the form Ax' <= BAx + b, where B
   has only positive entries and b is a vector of polynomials in
   recurrence terms at lower strata. *)
let _extract_matrix_leq srk wedge tr_symbols term_of_id =
  let open Apron in
  let cs = Wedge.coordinate_system wedge in
  let man = Polka.manager_alloc_loose () in
  let coeff_of_qq = Coeff.s_of_mpqf in
  let qq_of_coeff = function
    | Coeff.Scalar (Scalar.Float k) -> QQ.of_float k
    | Coeff.Scalar (Scalar.Mpqf k)  -> k
    | Coeff.Scalar (Scalar.Mpfrf k) -> Mpfrf.to_mpqf k
    | Coeff.Interval _ -> assert false
  in
  let linexpr_of_vec vec =
    let mk (coeff, id) = (coeff_of_qq coeff, id) in
    let (const_coeff, rest) = V.pivot CS.const_id vec in
    Linexpr0.of_list None
      (BatList.of_enum (BatEnum.map mk (V.enum rest)))
      (Some (coeff_of_qq const_coeff))
  in
  let vec_of_linexpr linexpr =
    let vec = ref V.zero in
    linexpr |> Linexpr0.iter (fun coeff dim ->
        vec := V.add_term (qq_of_coeff coeff) dim (!vec));
    V.add_term (qq_of_coeff (Linexpr0.get_cst linexpr)) CS.const_id (!vec)
  in

  let tr_coord =
    try
      List.map (fun (s,s') ->
          (CS.cs_term_id cs (`App (s, [])),
           CS.cs_term_id cs (`App (s', []))))
        tr_symbols
      |> Array.of_list
    with Not_found -> assert false
  in

  let rec fix polyhedron =
    let open Lincons0 in
    (* Polyhedron is of the form Ax' <= Bx + Cy, or equivalently,
       [-A B C]*[x' x y] >= 0. constraints is an array consisting of the
       rows of [-A B C].  *)
    logf "Polyhedron: %a"
      (Abstract0.print
         ((SrkUtil.mk_show (Term.pp srk)) % CS.term_of_coordinate cs))
      polyhedron;
    let constraints = DArray.create () in
    Abstract0.to_lincons_array man polyhedron
    |> Array.iter (fun lincons ->
        let vec = vec_of_linexpr lincons.linexpr0 in
        DArray.add constraints vec;
        if lincons.typ = EQ then
          DArray.add constraints (V.negate vec));
    let nb_constraints = DArray.length constraints in

    (* vu_cone is the cone { [v u] : u >= 0, v >= 0 uA = vB } *)
    let vu_cone =
      let pos_constraints = (* u >= 0, v >= 0 *)
        Array.init (2 * nb_constraints) (fun i ->
            Lincons0.make
              (Linexpr0.of_list None [(coeff_of_qq QQ.one, i)] None)
              SUPEQ)
        |> Abstract0.of_lincons_array man 0 (2 * nb_constraints)
      in
      Array.init (Array.length tr_coord) (fun i ->
          let (pre, post) = tr_coord.(i) in
          let linexpr = Linexpr0.make None in
          for j = 0 to nb_constraints - 1 do
            let vec = DArray.get constraints j in
            Linexpr0.set_coeff linexpr j (coeff_of_qq (V.coeff pre vec));
            Linexpr0.set_coeff
              linexpr
              (j + nb_constraints)
              (coeff_of_qq (V.coeff post vec));
          done;
          Lincons0.make linexpr Lincons0.EQ)
      |> Abstract0.meet_lincons_array man pos_constraints
    in
    (* Project vu_cone onto the v dimensions and compute generators. *)
    let v_generators =
      Abstract0.remove_dimensions
        man
        vu_cone
        { Dim.dim =
            (Array.init nb_constraints (fun i -> nb_constraints + i));
          Dim.intdim = 0;
          Dim.realdim = nb_constraints }
      |> Abstract0.to_generator_array man
    in
    (* new_constraints is v_generators * [-A B C]*)
    let new_constraints =
      Array.fold_right (fun gen nc ->
          let open Generator0 in
          let vec = vec_of_linexpr gen.linexpr0 in
          let row =
            BatEnum.fold (fun new_row (coeff, dim) ->
                assert (dim < nb_constraints);
                V.scalar_mul coeff (DArray.get constraints dim)
                |> V.add new_row)
              V.zero
              (V.enum vec)
            |> linexpr_of_vec
          in
          assert (QQ.equal QQ.zero (V.coeff CS.const_id vec));
          if gen.typ = RAY then
            (Lincons0.make row Lincons0.SUPEQ)::nc
          else if gen.typ = VERTEX then begin
            assert (V.equal V.zero vec); (* should be the origin *)
            nc
          end else
            assert false)
        v_generators
        []
      |> Array.of_list
    in
    let new_polyhedron =
      Abstract0.of_lincons_array man 0 (CS.dim cs) new_constraints
    in
    if Abstract0.is_eq man polyhedron new_polyhedron then
      if nb_constraints = 0 then
        (QQMatrix.zero,
         Array.make 0 (Array.make 0 QQ.zero),
         Array.make 0 QQXs.zero)
      else
        let mA =
          BatEnum.fold (fun mA i ->
              let row =
                BatEnum.fold (fun row j ->
                    let (pre, post) = tr_coord.(j) in
                    V.add_term
                      (QQ.negate (V.coeff post (DArray.get constraints i)))
                      pre
                      row)
                  V.zero
                  (0 -- (Array.length tr_coord - 1))
              in
              QQMatrix.add_row i row mA)
            QQMatrix.zero
            (0 -- (nb_constraints - 1))
        in

        (* Find a non-negative M such that B=M*A *)
        let m_entries = (* corresponds to one generic row of M *)
          Array.init nb_constraints (fun _ -> mk_symbol srk `TyReal)
        in
        (* Each entry of M must be non-negative *)
        let pos_constraints =
          List.map (fun sym ->
              mk_leq srk (mk_real srk QQ.zero) (mk_const srk sym))
            (Array.to_list m_entries)
        in
        let m_times_a =
          (0 -- (Array.length tr_coord - 1))
          /@ (fun i ->
              let pre = fst (tr_coord.(i)) in
              (0 -- (nb_constraints - 1))
              /@ (fun j ->
                  mk_mul srk [mk_const srk m_entries.(j);
                              mk_real srk (QQMatrix.entry j pre mA)])
              |> BatList.of_enum
              |> mk_add srk)
          |> BatArray.of_enum
        in
        (* B[i,j] = M[i,1]*A[1,j] + ... + M[i,n]*A[n,j] *)
        let mB =
          Array.init nb_constraints (fun i ->
              let row_constraints =
                (0 -- (Array.length tr_coord - 1))
                /@ (fun j ->
                    let pre = fst (tr_coord.(j)) in
                    mk_eq srk
                      m_times_a.(j)
                      (mk_real srk (V.coeff pre (DArray.get constraints i))))
                |> BatList.of_enum
              in
              let s = Smt.mk_solver srk in
              Smt.Solver.add s pos_constraints;
              Smt.Solver.add s row_constraints;
              let model =
                (* First try for a simple recurrence, then fall back *)
                Smt.Solver.push s;
                (0 -- (Array.length m_entries - 1))
                /@ (fun j ->
                    if i = j then
                      mk_true srk
                    else
                      mk_eq srk
                        (mk_const srk m_entries.(j))
                        (mk_real srk QQ.zero))
                |> BatList.of_enum
                |> Smt.Solver.add s;
                match Smt.Solver.get_model s with
                | `Sat model -> model
                | _ ->
                  Smt.Solver.pop s 1;
                  match Smt.Solver.get_model s with
                  | `Sat model -> model
                  | _ -> assert false
              in
              Array.init nb_constraints (fun i ->
                  Interpretation.real model m_entries.(i)))
        in
        let pvc =
          Array.init nb_constraints (fun i ->
              QQXs.scalar (V.coeff CS.const_id (DArray.get constraints i)))
        in
        (mA,mB,pvc)
    else
      fix (Abstract0.widening man polyhedron new_polyhedron)
  in
  (* TODO: reduce each halfspace *)
  let polyhedron =
    let constraints =
      BatList.filter_map
        (function
          | (`Eq, vec) ->
            Some (Lincons0.make (linexpr_of_vec vec) Lincons0.EQ)
          | (`Geq, vec) ->
            Some (Lincons0.make (linexpr_of_vec vec) Lincons0.SUPEQ))
        (Wedge.polyhedron wedge)
      |> Array.of_list
    in
    Abstract0.of_lincons_array
      man
      0
      (CS.dim cs)
      constraints
  in
  let tr_coord_set =
    Array.fold_left
      (fun set (d,d') -> IntSet.add d (IntSet.add d' set))
      IntSet.empty
      tr_coord
  in
  let forget =
    let non_tr_coord =
      BatEnum.fold (fun non_tr dim ->
          if IntSet.mem dim tr_coord_set then
            non_tr
          else
            dim::non_tr)
        []
        (0 -- (CS.dim cs - 1))
    in
    Array.of_list (List.rev non_tr_coord)
  in
  let polyhedron =
    Abstract0.forget_array
      man
      polyhedron
      forget
      false
  in
  let (mA, blk_transform, blk_add) = fix polyhedron in
  let size = Array.length blk_add in
  for i = 0 to size - 1 do
    DArray.add term_of_id (CS.term_of_vec cs (QQMatrix.row i mA))
  done;
  [{ blk_transform; blk_add }]


(* Find constant symbols in a wedge, and initialize the solvable
   polynomial map & simulation.  Should be called first. *)
let extract_constant_symbols srk tr_symbols wedge =
  let cs = Wedge.coordinate_system wedge in
  let pre_symbols = TF.pre_symbols tr_symbols in
  let post_symbols = TF.post_symbols tr_symbols in
  tr_symbols |> List.iter (fun (s,s') ->
      CS.admit_cs_term cs (`App (s, []));
      CS.admit_cs_term cs (`App (s', [])));

  let term_of_id = DArray.create () in

  (* Detect constant terms *)
  let is_symbolic_constant x =
    not (Symbol.Set.mem x pre_symbols || Symbol.Set.mem x post_symbols)
  in
  let constant_symbols =
    ref (Symbol.Set.of_list [get_named_symbol srk "log";
                             get_named_symbol srk "pow"])
  in
  for i = 0 to CS.dim cs - 1 do
    let term = CS.term_of_coordinate cs i in
    match Term.destruct srk term with
    | `App (sym, []) ->
      if is_symbolic_constant sym then begin
        constant_symbols := Symbol.Set.add sym (!constant_symbols);
        DArray.add term_of_id term
      end
    | _ ->
      if Symbol.Set.subset (symbols term) (!constant_symbols) then
        DArray.add term_of_id term
  done;
  term_of_id

let exp_ocrs srk tr_symbols loop_counter iter =
  let open OCRS in
  let open Type_def in

  Nonlinear.ensure_symbols srk;

  let post_map = (* map pre-state vars to post-state vars *)
    TF.post_map srk tr_symbols
  in

  let postify =
    let subst sym =
      if Symbol.Map.mem sym post_map then
        Symbol.Map.find sym post_map
      else
        mk_const srk sym
    in
    substitute_const srk subst
  in

  (* pre subscript *)
  let ss_pre = SSVar "k" in

  let constant_blocks =
    let const =
      { blk_transform = [|[|QQ.one|]|];
        blk_add = [| QQXs.zero |] }
    in
    BatEnum.repeat ~times:iter.nb_constants const
    |> BatList.of_enum
  in
  let sp = constant_blocks @ iter.block_eq @ iter.block_leq in
  let cf = closure_ocrs sp in
  let nb_equations = nb_equations iter in
  let term_of_expr =
    let pre_term_of_id name =
      iter.term_of_id.(int_of_string name)
    in
    let post_term_of_id name =
      let id = int_of_string name in
      postify (iter.term_of_id.(id))
    in
    term_of_ocrs srk loop_counter pre_term_of_id post_term_of_id
  in
  let mk_int k = mk_real srk (QQ.of_int k) in

  (iter.nb_constants -- ((Array.length cf) - 1))
  /@ (fun i ->
      let outvar = Output_variable (string_of_int i, ss_pre) in
      let PieceWiseIneq (ivar, pieces) =
        Deshift.deshift_ineq (Equals (outvar, cf.(i)))
      in
      assert (ivar = "k");
      let piece_to_formula (ivl, ineq) =
        let hypothesis = match ivl with
          | Bounded (lo, hi) ->
            mk_and srk [mk_leq srk (mk_int lo) loop_counter;
                        mk_leq srk loop_counter (mk_int hi)]
          | BoundBelow lo ->
            mk_and srk [mk_leq srk (mk_int lo) loop_counter]
        in
        let conclusion = match ineq with
          | Equals (x, y) ->
            if i < (iter.nb_constants + nb_equations) then
              mk_eq srk (term_of_expr x) (term_of_expr y)
            else
              mk_leq srk (term_of_expr x) (term_of_expr y)
          | _ -> assert false
        in
        mk_if srk hypothesis conclusion
      in
      mk_and srk (List.map piece_to_formula pieces))
  |> BatList.of_enum
  |> mk_and srk

let wedge_of srk tr_symbols iter =
  let post_map =
    List.fold_left
      (fun map (sym, sym') -> Symbol.Map.add sym sym' map)
      Symbol.Map.empty
      tr_symbols
  in
  let postify =
    let subst sym =
      if Symbol.Map.mem sym post_map then
        mk_const srk (Symbol.Map.find sym post_map)
      else
        mk_const srk sym
    in
    substitute_const srk subst
  in
  let rec_atoms mk_compare offset recurrence =
    recurrence.blk_transform |> Array.mapi (fun i row ->
        let term = iter.term_of_id.(offset + i) in
        let rhs_add =
          QQXs.term_of
            srk
            (fun j -> iter.term_of_id.(j))
            recurrence.blk_add.(i)
        in
        let rhs =
          BatArray.fold_lefti (fun rhs j coeff ->
              if QQ.equal coeff QQ.zero then
                rhs
              else
                let jterm =
                  mk_mul srk [mk_real srk coeff;
                              iter.term_of_id.(offset + j)]
                in
                jterm::rhs)
            [rhs_add]
            row
          |> mk_add srk
        in
        mk_compare (postify term) rhs)
    |> BatArray.to_list
  in
  let (offset, atoms) =
    BatList.fold_left (fun (offset, atoms) recurrence ->
        let size = Array.length recurrence.blk_add in
        (offset+size,
         (rec_atoms (mk_eq srk) offset recurrence)@atoms))
      (iter.nb_constants, [])
      iter.block_eq
  in
  let (_, atoms) =
    BatList.fold_left (fun (offset, atoms) recurrence ->
        let size = Array.length recurrence.blk_add in
        (offset+size,
         (rec_atoms (mk_leq srk) offset recurrence)@atoms))
      (offset, atoms)
      iter.block_leq
  in
  Wedge.of_atoms srk atoms

let equal srk tr_symbols iter iter' =
  Wedge.equal (wedge_of srk tr_symbols iter) (wedge_of srk tr_symbols iter')

module SolvablePolynomialOne = struct
  type nonrec 'a t = 'a t

  (* Extract stratified recurrences of the form x' = x + p, where p is a
     polynomial over induction variables of lower strata *)
  let extract_induction_vars srk wedge tr_symbols rec_terms =
    let cs = Wedge.coordinate_system wedge in

    let id_of_sym sym =
      try
        CS.cs_term_id cs (`App (sym, []))
      with Not_found -> assert false
    in

    (* An additive dimension is one that is allowed to appear as an additive
       term *)
    let cs_dim = CS.dim cs in
    let additive_dim x = x >= cs_dim in

    let rewrite =
      let elim_order =
        Monomial.block [not % additive_dim] Monomial.degrevlex
      in
      let rewrite =
        ref (Polynomial.Rewrite.mk_rewrite elim_order (Wedge.vanishing_ideal wedge)
             |> Polynomial.Rewrite.grobner_basis)
      in
      rec_terms |> DArray.iteri (fun i t ->
          let vec = CS.vec_of_term cs t in
          let p =
            QQXs.add_term
              (QQ.of_int (-1))
              (Monomial.singleton (i + cs_dim) 1)
              (QQXs.of_vec ~const:(CS.const_id) vec)
          in
          rewrite := (Polynomial.Rewrite.add_saturate (!rewrite) p));
      rewrite
    in
    let recurrences = ref [] in
    let transform_one = [|[|QQ.one|]|] in
    let delta s s' = (* s' - s *)
      QQXs.sub
        (QQXs.of_dim (id_of_sym s'))
        (QQXs.of_dim (id_of_sym s))
    in
    let add_recurrence s add =
      let polynomial =
        QQXs.sub
          (QQXs.of_dim (id_of_sym s))
          (QQXs.of_dim (cs_dim + (DArray.length rec_terms)))
      in
      let recur =
        { blk_transform = transform_one;
          blk_add = [|add|] }
      in
      DArray.add rec_terms (mk_const srk s);
      rewrite := (Polynomial.Rewrite.add_saturate (!rewrite) polynomial);
      recurrences := recur::(!recurrences)
    in
    let subst x =
      if additive_dim x then
        QQXs.of_dim (x - cs_dim)
      else
        raise IllFormedRecurrence
    in
    let continue = ref true in
    let non_induction = ref tr_symbols in
    while !continue do
      continue := false;
      non_induction :=
        List.filter (fun (s,s') ->
            try
              let add =
                delta s s'
                |> Polynomial.Rewrite.reduce (!rewrite)
                |> QQXs.substitute subst
              in
              add_recurrence s add;
              continue := true;
              false
            with IllFormedRecurrence -> true)
          (!non_induction)
    done;
    List.rev (!recurrences)

  let abstract_wedge srk tr_symbols wedge =
    let term_of_id = extract_constant_symbols srk tr_symbols wedge in
    let nb_constants = DArray.length term_of_id in
    let block_eq = extract_induction_vars srk wedge tr_symbols term_of_id in
    let block_leq = extract_vector_leq srk wedge tr_symbols term_of_id QQ.one in
    { nb_constants;
      term_of_id = DArray.to_array term_of_id;
      block_eq = block_eq;
      block_leq = block_leq }

  let abstract srk tf =
    abstract_wedge srk (TF.symbols tf) (TF.wedge_hull srk tf)

  let join srk tr_symbols iter iter' =
    Wedge.join (wedge_of srk tr_symbols iter) (wedge_of srk tr_symbols iter')
    |> abstract_wedge srk tr_symbols

  let widen srk tr_symbols iter iter' =
    Wedge.widen (wedge_of srk tr_symbols iter) (wedge_of srk tr_symbols iter')
    |> abstract_wedge srk tr_symbols

  let exp = exp_ocrs
  let equal = equal
  let pp = pp
end

module SolvablePolynomial = struct
  type nonrec 'a t = 'a t

  let abstract_wedge srk tr_symbols wedge =
    let term_of_id = extract_constant_symbols srk tr_symbols wedge in
    let nb_constants = DArray.length term_of_id in
    let block_eq = extract_solvable_polynomial_eq srk wedge tr_symbols term_of_id in
    let block_leq = extract_vector_leq srk wedge tr_symbols term_of_id QQ.one in
    { nb_constants;
      term_of_id = DArray.to_array term_of_id;
      block_eq = block_eq;
      block_leq = block_leq }

  let abstract srk tf =
    abstract_wedge srk (TF.symbols tf) (TF.wedge_hull srk tf)

  let join srk tr_symbols iter iter' =
    Wedge.join (wedge_of srk tr_symbols iter) (wedge_of srk tr_symbols iter')
    |> abstract_wedge srk tr_symbols

  let widen srk tr_symbols iter iter' =
    Wedge.widen (wedge_of srk tr_symbols iter) (wedge_of srk tr_symbols iter')
    |> abstract_wedge srk tr_symbols

  let equal = equal
  let pp = pp
  let exp = exp_ocrs
end

module SolvablePolynomialPeriodicRational = struct
  type nonrec 'a t = 'a t

  let abstract_wedge srk tr_symbols wedge =
    let term_of_id = extract_constant_symbols srk tr_symbols wedge in
    let nb_constants = DArray.length term_of_id in
    let block_eq = extract_periodic_rational_matrix_eq srk wedge tr_symbols term_of_id in
    let block_leq = extract_vector_leq srk wedge tr_symbols term_of_id QQ.one in
    { nb_constants;
      term_of_id = DArray.to_array term_of_id;
      block_eq = block_eq;
      block_leq = block_leq }

  let abstract srk tf =
    abstract_wedge srk (TF.symbols tf) (TF.wedge_hull srk tf)

  let exp srk tr_symbols loop_counter iter =
    Nonlinear.ensure_symbols srk;
    let srk = srk in

    let post_map = (* map pre-state vars to post-state vars *)
      TF.post_map srk tr_symbols
    in
    let postify =
      let subst sym =
        if Symbol.Map.mem sym post_map then
          Symbol.Map.find sym post_map
        else
          mk_const srk sym
      in
      substitute_const srk subst
    in

    let constant_blocks =
      let const =
        { blk_transform = [|[|QQ.one|]|];
          blk_add = [| QQXs.zero |] }
      in
      BatEnum.repeat ~times:iter.nb_constants const
      |> BatList.of_enum
    in
    let sp = constant_blocks @ iter.block_eq @ iter.block_leq in
    let cf = closure_periodic_rational sp in

    (* For each period p, maintain a pair (q, r) such that loop_counter = qp + r *)
    let qr_map = BatHashtbl.create 97 in
    Hashtbl.add qr_map 1 (loop_counter, mk_real srk QQ.zero);
    let get_qr n =
      if Hashtbl.mem qr_map n then
        Hashtbl.find qr_map n
      else
        let loop_q = mk_const srk (mk_symbol srk ~name:"q" `TyInt) in
        let loop_r = mk_const srk (mk_symbol srk ~name:"r" `TyInt) in
        Hashtbl.add qr_map n (loop_q, loop_r);
        (loop_q, loop_r)
    in
    let nb_equations = nb_equations iter in
    let closed =
      (iter.nb_constants -- (Array.length iter.term_of_id - 1))
      /@ (fun i ->
          let lhs = postify iter.term_of_id.(i) in
          assert (i < (Array.length cf));
          let rhs =
            (UPXs.enum cf.(i))
            /@ (fun (up, m) ->
                let m = Monomial.term_of srk (fun i -> iter.term_of_id.(i)) m in
                let (loop_q, loop_r) = get_qr (UP.period_len up) in
                let up = UP.term_of srk loop_q loop_r up in
                mk_mul srk [up; m])
            |> BatList.of_enum
            |> mk_add srk
          in
          if i < (iter.nb_constants + nb_equations) then
            mk_eq srk lhs rhs
          else
            mk_leq srk lhs rhs)
      |> BatList.of_enum
      |> mk_and srk
    in
    let qr_constraints =
      Hashtbl.fold (fun n (q, r) rest ->
          if n = 0 then
            rest
          else
            let n = mk_real srk (QQ.of_int n) in
            (* loop_counter = qn + r /\ 0 <= r < n *)
            (mk_eq srk
               loop_counter
               (mk_add srk [mk_mul srk [q; n]; r]))
            ::(mk_lt srk r n)
            ::(mk_leq srk (mk_real srk QQ.zero) r)
            ::rest)
        qr_map
        []
      |> mk_and srk
    in
    mk_and srk [closed; qr_constraints]

  let join srk tr_symbols iter iter' =
    Wedge.join (wedge_of srk tr_symbols iter) (wedge_of srk tr_symbols iter')
    |> abstract_wedge srk tr_symbols

  let widen srk tr_symbols iter iter' =
    Wedge.widen (wedge_of srk tr_symbols iter) (wedge_of srk tr_symbols iter')
    |> abstract_wedge srk tr_symbols

  let equal = equal
  let pp = pp
end

module PresburgerGuard = struct
  module SPPR = SolvablePolynomialPeriodicRational
  include Iteration.Product(SPPR)(Iteration.PolyhedronGuard)

  (* Given a term of the form floor(x/d) with d a positive int, retrieve the pair (x,d) *)
  let destruct_idiv srk t =
    match Term.destruct srk t with
    | `Unop (`Floor, t) -> begin match Term.destruct srk t with
        | `Binop (`Div, num, den) -> begin match Term.destruct srk den with
            | `Real den -> begin match QQ.to_int den with
                | Some den when den > 0 -> Some (num, den)
                | _ -> None
              end
            | _ -> None
          end
        | _ -> None
      end
    | _ -> None

  let idiv_to_ite srk expr =
    match Expr.refine srk expr with
    | `Term t -> begin match destruct_idiv srk t with
        | Some (num, den) when den < 10 ->
          let den_term = mk_real srk (QQ.of_int den) in
          let num_over_den =
            mk_mul srk [mk_real srk (QQ.of_frac 1 den); num]
          in
          let offset =
            BatEnum.fold (fun else_ r ->
                let remainder_is_r =
                  mk_eq srk
                    (mk_mod srk (mk_sub srk num (mk_real srk (QQ.of_int r))) den_term)
                    (mk_real srk QQ.zero)
                in
                mk_ite srk
                  remainder_is_r
                  (mk_real srk (QQ.of_frac (-r) den))
                  else_)
              (mk_real srk QQ.zero)
              (1 -- (den-1))
          in
          (mk_add srk [num_over_den; offset] :> ('a,typ_fo) expr)
        | _ -> expr
      end
    | _ -> expr

  (* Over-approximate a formula with a Presbuger formula.  Requires
     expression to be in negation normal form *)
  let abstract_presburger_rewriter srk expr =
    match Expr.refine srk expr with
    | `Formula phi -> begin match Formula.destruct srk phi with
        | `Atom (_, _, _) ->
          if Quantifier.is_presburger_atom srk phi then
            expr
          else
            (mk_true srk :> ('a,typ_fo) expr)
        | _ -> expr
      end
    | _ -> expr

  let abstract_presburger srk phi =
    let nnf_simplify expr =
      nnf_rewriter srk expr(*(SrkSimplify.simplify_terms_rewriter srk expr)*)
    in
    rewrite srk ~up:(idiv_to_ite srk) phi
    |> eliminate_ite srk
    |> rewrite srk ~down:nnf_simplify ~up:(abstract_presburger_rewriter srk)

  let exp srk tr_symbols loop_counter (sp, guard) =
    let module G = Iteration.PolyhedronGuard in
    let precondition = SrkApron.formula_of_property (G.precondition guard) in
    let postcondition = SrkApron.formula_of_property (G.postcondition guard) in
    let pre_symbols = (* + symbolic constants *)
      Symbol.Set.union (symbols precondition) (TF.pre_symbols tr_symbols)
    in
    let post_symbols = TF.post_symbols tr_symbols in
    let post_map = TF.post_map srk tr_symbols in

    (* Let cf(k,x,x') be the closed form of the affine map associated
       with sp.  The presburger guard is
          (forall 0 <= p < k, there exists y' such that cf(p,x,y') /\ pre(y'))

       The existential quantifier is safe to over-approximate (by a Presburger formula),
       and the universal quantifier eliminated precisely. *)
    let presburger_guard =
      let prev_counter_sym = mk_symbol srk ~name:"p" `TyInt in
      let prev_counter = mk_const srk prev_counter_sym in

      (* "fresh" set of post-state variables, to be existentially
         quantified *)
      let fresh_symbols = ref Symbol.Set.empty in
      let fresh =
        Memo.memo (fun s ->
            let name = "_" ^ (show_symbol srk s) in
            let sym = mk_symbol srk ~name (typ_symbol srk s) in
            fresh_symbols := Symbol.Set.add sym (!fresh_symbols);
            sym)
      in
      let freshify = substitute_const srk (fun s ->
          if Symbol.Set.mem s post_symbols then
            mk_const srk (fresh s)
          else
            mk_const srk s)
      in

      let fresh_tr_symbols =
        List.map (fun (s,s') -> (s, fresh s')) tr_symbols
      in

      let closed =
        let sp' =
          let block_eq =
            if List.length sp.block_eq > 0 then [List.hd sp.block_eq] else []
          in
          let term_of_id =
            (* Maintain invariant that the length of term_of_id is
               equal to the dimension of the underlying solvable
               polynomial map *)
            Array.init
              (sp.nb_constants + (dimension block_eq))
              (fun i -> sp.term_of_id.(i))
          in
          { nb_constants = sp.nb_constants;
            block_eq = block_eq;
            block_leq = [];
            term_of_id = term_of_id }
        in
        SPPR.exp srk fresh_tr_symbols prev_counter sp'
      in

      let prev_guard =
        let fresh_pre = (* precondition, expressed over fresh symbols *)
          substitute_const srk
            (fun s ->
               if Symbol.Map.mem s post_map then
                 freshify (Symbol.Map.find s post_map)
               else
                 mk_const srk s)
            precondition
        in
        abstract_presburger srk (mk_and srk [fresh_pre; closed])
      in
      let exists_prev_guard =
        let allowed_symbols =
          Array.fold_left (fun set term ->
              Symbol.Set.union set (symbols term))
            (Symbol.Set.add prev_counter_sym pre_symbols)
            sp.term_of_id
        in
        Quantifier.mbp srk (fun x -> Symbol.Set.mem x allowed_symbols) prev_guard
      in
      mk_if srk
        (mk_and srk [mk_leq srk (mk_real srk QQ.zero) prev_counter;
                     mk_lt srk prev_counter loop_counter])
        (abstract_presburger srk exists_prev_guard)
      |> mk_not srk
      |> Quantifier.mbp srk (fun x -> x != prev_counter_sym)
      |> mk_not srk
      |> rewrite srk ~down:(nnf_rewriter srk) ~up:(SrkSimplify.simplify_terms_rewriter srk)
    in

    let guard_closure =
      mk_or srk [mk_and srk [mk_eq srk loop_counter (mk_real srk QQ.zero);
                             TF.formula (TF.identity srk tr_symbols)];
                 mk_and srk [mk_leq srk (mk_real srk QQ.one) loop_counter;
                             presburger_guard;
                             precondition;
                             postcondition]]
    in
    mk_and srk [SPPR.exp srk tr_symbols loop_counter sp;
                guard_closure]

end

type 'a dlts_abstraction =
  { dlts : PLM.t;
    simulation : ('a term) array }

module DLTS = struct
  module VS = Linear.QQVectorSpace
  module V = Linear.QQVector
  module M = Linear.QQMatrix

  type 'a t = 'a dlts_abstraction

  let dimension iter = Array.length iter.simulation

  let pp srk _ formatter iter =
    let sim i = iter.simulation.(i) in
    Format.fprintf formatter "@[<v 2>Map:";
    iter.simulation |> BatArray.iteri (fun i term ->
        let row =
          Linear.term_of_vec srk sim (QQMatrix.row i (PLM.map iter.dlts))
        in
        Format.fprintf formatter "@;%a := %a"
          (Term.pp srk) term
          (Term.pp srk) row);
    Format.fprintf formatter "@]";
    if (PLM.guard iter.dlts) != [] then begin
      Format.fprintf formatter "@;@[<v 2>when:";
      (PLM.guard iter.dlts) |> List.iter (fun eq ->
          Format.fprintf formatter "@;%a = 0"
            (Term.pp srk) (Linear.term_of_vec srk sim eq));
      Format.fprintf formatter "@]"
    end

  let exp_impl base_exp srk tr_symbols loop_count iter =
    let sim i = iter.simulation.(i) in
    let post_map = (* map pre-state vars to post-state vars *)
      TF.post_map srk tr_symbols
    in
    let postify =
      let subst sym =
        if Symbol.Map.mem sym post_map then
          Symbol.Map.find sym post_map
        else
          mk_const srk sym
      in
      substitute_const srk subst
    in
    let zero = mk_real srk QQ.zero in

    let dim = dimension iter in

    (* Iterate function until the guard stabilizes (i.e., dom(f^n) =
       dom(f^{n+1})).  *)
    let rec fix g i =
      let h = PLM.compose iter.dlts g in
      if VS.dimension (PLM.guard g) == dim then
        (* Invariant domain is trivial.  Since one dimension of the
           domain represents the constant 1, this is inconsistent. *)
        mk_false srk
      else if VS.equal (PLM.guard g) (PLM.guard h) then

        (* stable_transform has the same action as f on the invariant
           domain, and sends everything orthogonal to the invariant
           domain to 0.  *)
        let stable_transform = PLM.map (PLM.make (PLM.map iter.dlts) (PLM.guard g)) in

        let closed =
          let underlying_block =
            { blk_transform = QQMatrix.dense_of stable_transform dim dim;
              blk_add = Array.make dim QQXs.zero }
          in
          let underlying_iter =
            { term_of_id = iter.simulation;
              nb_constants = 0;
              block_eq = [underlying_block];
              block_leq = [] }
          in
          base_exp srk tr_symbols loop_count underlying_iter
        in
        let domain_constraints =
          List.map (fun t ->
              let term = Linear.term_of_vec srk sim t in
              mk_eq srk term zero)
            (PLM.guard g)
          |> mk_and srk
        in
        mk_and srk [ closed
                   ; domain_constraints
                   ; mk_leq srk (mk_real srk (QQ.of_int i)) loop_count ]
      else
        let transform =
          (0 -- (dim - 1))
          /@ (fun i ->
              let lhs = postify (sim i) in
              let rhs =
                Linear.term_of_vec srk sim (QQMatrix.row i (PLM.map g))
              in
              mk_eq srk lhs rhs)
          |> BatList.of_enum
        in
        let guard =
          List.map
            (fun t -> mk_eq srk zero (Linear.term_of_vec srk sim t))
            (PLM.guard g)
        in
        mk_or srk [ mk_and srk (mk_eq srk (mk_real srk (QQ.of_int i)) loop_count
                                ::(guard @ transform))
                  ; fix h (i+1) ]
    in
    if dim = 0 then mk_true srk
    else fix (PLM.identity dim) 0

  let exp srk tr_symbols loop_count iter =
    exp_impl SolvablePolynomial.exp srk tr_symbols loop_count iter

  let abstract srk tf =
    let tr_symbols = TF.symbols tf in
    let phi = Nonlinear.linearize srk (TF.formula tf) in
    let phi_symbols =
      Symbol.Set.filter (fun s -> typ_symbol srk s = `TyInt && TF.exists tf s) (symbols phi)
      |> Symbol.Set.elements
    in
    let constants = Symbol.Set.elements (TF.symbolic_constants tf) in
    (* pre_map is a mapping from dimensions that correspond to
       post-state dimensions to their pre-state counterparts *)
    let pre_map =
      List.fold_left (fun pre_map (s,s') ->
          let pre = Linear.dim_of_sym s in
          let post = Linear.dim_of_sym s' in
          IntMap.add post pre pre_map)
        IntMap.empty
        tr_symbols
    in
    let (mA, mB, nb_rows) =
      BatList.fold_left (fun (mA, mB, i) t ->
          logf "Equation: %a = 0" (Term.pp srk) t;
          let (a, b) =
            BatEnum.fold (fun (a, b) (coeff, id) ->
                if IntMap.mem id pre_map then
                  (V.add_term (QQ.negate coeff) (IntMap.find id pre_map) a, b)
                else if id == Linear.const_dim then
                  (a, V.add_term coeff Linear.const_dim b)
                else
                  (a, V.add_term coeff id b))
              (V.zero, V.zero)
              (V.enum (Linear.linterm_of srk t))
          in
          (QQMatrix.add_row i a mA, QQMatrix.add_row i b mB, i + 1))
        (QQMatrix.zero, QQMatrix.zero, 0)
        (Abstract.affine_hull srk phi phi_symbols)
    in
    let (mA, mB, _) =
      BatList.fold_left (fun (mA, mB, i) id ->
          (QQMatrix.add_row i (V.of_term QQ.one id) mA,
           QQMatrix.add_row i (V.of_term QQ.one id) mB,
           i + 1))
        (mA, mB, nb_rows)
        (Linear.const_dim::(List.map Linear.dim_of_sym constants))
    in
    let (dlts, mS) = Lts.determinize (mA, mB) in
    let simulation =
      QQMatrix.rowsi mS
      /@ (Linear.of_linterm srk % snd)
      |> BatArray.of_enum
    in
    let res = { dlts; simulation } in
    logf "Extracted:@? %a" (pp srk tr_symbols) res;
    res

  let equal _ _ iter1 iter2 =
    PLM.equal iter1.dlts iter2.dlts
    && BatArray.for_all2 Term.equal iter1.simulation iter2.simulation

  let to_formula srk iter =
    let sim i = iter.simulation.(i) in
    let map =
      (0 -- (dimension iter - 1))
      /@ (fun i ->
          let rhs =
            Linear.term_of_vec srk sim (QQMatrix.row i (PLM.map iter.dlts))
          in
          mk_eq srk (sim i) rhs)
      |> BatList.of_enum
      |> mk_and srk
    in
    let zero = mk_real srk QQ.zero in
    let guard =
      List.map
        (fun vec -> mk_eq srk zero (Linear.term_of_vec srk sim vec))
        (PLM.guard iter.dlts)
      |> mk_and srk
    in
    mk_and srk [map; guard]

  let join srk tr_symbols iter1 iter2 =
    abstract srk (TF.make
                    (mk_or srk [to_formula srk iter1;
                                to_formula srk iter2])
                    tr_symbols)

  let widen = join
end

module DLTSSolvablePolynomial = struct
  include DLTS
  let abstract_wedge srk tr_symbols wedge =
    let cs = Wedge.coordinate_system wedge in
    let sp_simulation = extract_constant_symbols srk tr_symbols wedge in
    let nb_constants = DArray.length sp_simulation in
    let block_eq = extract_solvable_polynomial_eq srk wedge tr_symbols sp_simulation in
    let pm =
      let id_block =
        { blk_transform = [| [| QQ.one |] |];
          blk_add = [| QQXs.zero |] }
      in
      let padded_blocks =
        BatEnum.fold
          (fun blocks _ -> id_block::blocks)
          block_eq
          (1 -- nb_constants)
      in
      to_polynomial_map padded_blocks
    in
    let pm_size = Array.length pm in
    let ideal =
      let shift_coords = QQXs.substitute (fun i -> QQXs.of_dim (i + pm_size)) in
      let sim_dim i = i < pm_size in
      let elim_order =
        Monomial.block [not % sim_dim] Monomial.degrevlex
      in
      DArray.fold_left (fun (ideal, i) t ->
          let q = CS.polynomial_of_term cs t in
          let p =
            QQXs.add_term
              (QQ.of_int (-1))
              (Monomial.singleton i 1)
              (shift_coords q)
          in
          (p::ideal, i + 1))
        (List.map shift_coords (Wedge.vanishing_ideal wedge), 0)
        sp_simulation
      |> fst
      |> Polynomial.Rewrite.mk_rewrite elim_order
      |> Polynomial.Rewrite.grobner_basis
      |> Polynomial.Rewrite.generators
      |> List.filter (fun p ->
          BatEnum.for_all
            (fun (_, m) ->
               BatEnum.for_all (fun (d, _) -> sim_dim d) (Monomial.enum m))
            (QQXs.enum p))
    in
    let (dlts, sim) = dlts_of_solvable_algebraic pm ideal in
    let (pr_dlts, pr_sim) =
      Lts.periodic_rational_spectrum_reflection dlts (Array.length sim)
    in
    let simulation =
      QQMatrix.rowsi pr_sim
      /@ (fun (_, row) ->
          (V.enum row)
          /@ (fun (coeff, dim) ->
              mk_mul srk [mk_real srk coeff;
                          Monomial.term_of srk (fun i -> DArray.get sp_simulation i) sim.(dim)])
          |> BatList.of_enum
          |> mk_add srk)
      |> BatArray.of_enum
    in
    { dlts = pr_dlts; simulation }

  let abstract srk tf =
    let tr_symbols = TF.symbols tf in
    let post_symbols = TF.post_symbols tr_symbols in
    let subterm x = not (Symbol.Set.mem x post_symbols) in
    let wedge =
      Wedge.abstract_equalities ~exists:(TF.exists tf) ~subterm srk (TF.formula tf)
    in
    abstract_wedge srk tr_symbols wedge

  let exp srk tr_symbols loop_count iter =
    exp_impl SolvablePolynomialPeriodicRational.exp srk tr_symbols loop_count iter
end

module DLTSPeriodicRational = struct
  include DLTS

  let compose_simulation srk mS simulation =
    QQMatrix.rowsi mS
    /@ (fun (_, row) ->
      Linear.term_of_vec srk (fun i -> simulation.(i)) row
      |> SrkSimplify.simplify_term srk)
    |> BatArray.of_enum

  let abstract srk tf =
    let { dlts; simulation } = DLTS.abstract srk tf in
    let (dlts, mS) =
      Lts.periodic_rational_spectrum_reflection dlts (Array.length simulation)
    in
    let simulation = compose_simulation srk mS simulation in
    { dlts; simulation }

  let abstract_rational srk tf =
    let { dlts; simulation } = DLTS.abstract srk tf in
    let (dlts, mS) =
      Lts.rational_spectrum_reflection dlts (Array.length simulation)
    in
    let simulation = compose_simulation srk mS simulation in
    { dlts; simulation }

  let exp srk tr_symbols loop_count iter =
    exp_impl SolvablePolynomialPeriodicRational.exp srk tr_symbols loop_count iter
end

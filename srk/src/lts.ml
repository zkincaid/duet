open BatPervasives
open Syntax

module QQMatrix = Linear.QQMatrix
module QQVector = Linear.QQVector
module QQVectorSpace = Linear.QQVectorSpace
module IntMap = SrkUtil.Int.Map
module TF = TransitionFormula

type lts = QQMatrix.t * QQMatrix.t

let pp pp_dim formatter (mA, mB) =
  let open Format in
  let pp_dim' formatter i = fprintf formatter "%a'" pp_dim i in
  fprintf formatter "@[<v 0>";
  SrkUtil.Int.Set.union (QQMatrix.row_set mA) (QQMatrix.row_set mB)
  |> SrkUtil.Int.Set.iter (fun i ->
         fprintf formatter "%a = %a@;"
           (QQVector.pp_term pp_dim') (QQMatrix.row i mA)
           (QQVector.pp_term pp_dim) (QQMatrix.row i mB));
  fprintf formatter "@]"

let containment_witness (mA, mB) (mA', mB') =
  Linear.divide_right
    (QQMatrix.interlace_columns mA' mB')
    (QQMatrix.interlace_columns mA mB)

let contains (mA, mA') (mB, mB') =
  match containment_witness (mA, mB) (mA', mB') with
  | Some _ -> true
  | None -> false

let abstract_lts srk tf =
  let tr_symbols = TF.symbols tf in
  let phi_symbols =
    Symbol.Set.filter (TF.exists tf) (symbols (TF.formula tf))
    |> Symbol.Set.elements
  in
  let constants = List.filter (TF.is_symbolic_constant tf) phi_symbols in
  (* pre_map is a mapping from dimensions that correspond to
     post-state dimensions to their pre-state counterparts *)
  let pre_map =
    List.fold_left (fun pre_map (s,s') ->
        let pre, post = Linear.dim_of_sym s, Linear.dim_of_sym s' in
        IntMap.add post pre pre_map)
      IntMap.empty
      tr_symbols
  in
  let (mA, mB, nb_rows) =
    BatList.fold_left (fun (mA, mB, i) t ->
        let (a, b) =
          BatEnum.fold (fun (a, b) (coeff, id) ->
              if IntMap.mem id pre_map then
                (QQVector.add_term (QQ.negate coeff) (IntMap.find id pre_map) a, b)
              else if id == Linear.const_dim then
                (a, QQVector.add_term coeff Linear.const_dim b)
              else
                (a, QQVector.add_term coeff id b))
            (QQVector.zero, QQVector.zero)
            (QQVector.enum (Linear.linterm_of srk t))
        in
        (QQMatrix.add_row i a mA, QQMatrix.add_row i b mB, i + 1))
      (QQMatrix.zero, QQMatrix.zero, 0)
      (Abstract.affine_hull srk (TF.formula tf) phi_symbols)
  in
  let (mA, mB, _) =
    BatList.fold_left (fun (mA, mB, i) id ->
        (QQMatrix.add_row i (QQVector.of_term QQ.one id) mA,
         QQMatrix.add_row i (QQVector.of_term QQ.one id) mB,
         i + 1))
      (mA, mB, nb_rows)
      (Linear.const_dim::(List.map Linear.dim_of_sym constants))
  in
  (mA, mB)

module PartialLinearMap = struct
  module V = QQVector
  module M = QQMatrix
  module VS = QQVectorSpace

  type t =
    { (* Each row should belong to domain *)
      map : M.t;

      (* Guard is the othogonal complement of the domain.  That is, v
         belongs to dom(f) iff it is orthogonal to every vector in
         guard. *)
      guard : VS.t }

  module IntMap = SrkUtil.Int.Map

  (* After normalization, we have:
     1. the vectors in guard are linearly independent
     2. map sends every vector orthogonal to the domain to 0 *)
  let normalize f =
    let guard = VS.basis f.guard in
    let mG = VS.matrix_of guard in
    let dims =
      SrkUtil.Int.Set.elements (SrkUtil.Int.Set.union (M.column_set f.map) (M.column_set mG))
    in
    let dom = Linear.nullspace mG dims in
    (* Expansion in the basis formed by the domain and its orthogonal
       complement (guard). *)
    let basis_change =
      match Linear.divide_left (M.identity dims) (M.transpose (VS.matrix_of (dom @ guard))) with
      | None -> assert false
      | Some cob -> cob
    in
    let map =
      M.mul (M.mul f.map (M.transpose (VS.matrix_of dom))) basis_change
    in
    dom |> List.iter (fun x ->
        assert (V.equal (Linear.vector_right_mul f.map x) (Linear.vector_right_mul map x)));
    f.guard |> List.iter (fun x ->
        assert (V.equal V.zero (Linear.vector_right_mul map x)));
    { map; guard }

  let equal f g =
    M.equal f.map g.map
    && VS.equal f.guard g.guard

  let identity dim =
    { map = QQMatrix.identity (BatList.of_enum (0 -- (dim - 1)));
      guard = [] }

  let make map guard =
    normalize { map; guard }

  let pp formatter f =
    Format.fprintf formatter "@[ %a@;Subject to: {@[%a@]}@]"
      M.pp f.map
      (SrkUtil.pp_print_enum V.pp) (BatList.enum f.guard)

  let compose f g =
    let guard =
      M.rowsi (M.mul (VS.matrix_of f.guard) g.map)
      /@ snd
      |> BatList.of_enum
      |> VS.sum g.guard
    in
    { map = M.mul f.map g.map;
      guard = guard }
    |> normalize

  let iteration_sequence f =
    let rec fix g =
      let h = compose f g in
      if VS.equal g.guard h.guard then
        ([g], g.guard)
      else
        let (seq, stable) = fix h in
        (g::seq, stable)
    in
    fix f

  let map f = f.map
  let guard f = f.guard
end

type dlts = PartialLinearMap.t 

(* A and B, find a matrix C whose rows constitute a basis for the
   vector space { v : exists u. uA = vB } *)
let max_rowspace_projection mA mB = 
  (* Create a system u*A - v*B = 0.  u's occupy even columns and v's occupy
     odd. *)
  let mat =
    ref (QQMatrix.interlace_columns
           (QQMatrix.transpose mA)
           (QQMatrix.transpose (QQMatrix.scalar_mul (QQ.of_int (-1)) mB)))
  in
  let c = ref [] in
  let mat_rows =
    ref (BatEnum.fold (fun m (i, _) -> max m i) 0 (QQMatrix.rowsi (!mat)) + 1)
  in

  (* Loop through the columns col of A/B, trying to find a vector u and v such
     that uA = vB and v has 1 in col's entry.  If yes, add v to C, and add a
     constraint to mat that (in all future rows of C), col's entry is 0.  This
     ensures that the rows of C are linearly independent. *)
  (* to do: repeatedly solving super systems of the same system of equations
       -- can be made more efficient *)
  (QQMatrix.rowsi mB)
  |> (BatEnum.iter (fun (r, _) ->
      let col = 2*r + 1 in
      let mat' =
        QQMatrix.add_row
          (!mat_rows)
          (QQVector.of_term QQ.one col)
          (!mat)
      in
      match Linear.solve mat' (QQVector.of_term QQ.one (!mat_rows)) with
      | Some solution ->
        let c_row =
          BatEnum.fold (fun c_row (entry, i) ->
              if i mod 2 = 1 then
                QQVector.add_term entry (i/2) c_row
              else
                c_row)
            QQVector.zero
            (QQVector.enum solution)
        in
        assert (not (QQVector.equal c_row QQVector.zero));
        c := c_row :: (!c);
        mat := mat';
        incr mat_rows
      | None -> ()));
  !c

(* Given an LTS Ax' = Bx, find a basis for the space of functionals
   that are determined on the LTS; i.e.,
     { f : forall u,v,w. Av = Bu /\ Aw = Bu ==> f(v) = f(w) }
   or equivalently,
     { f : exists g. gA = fB } *)
let determinize (mA, mB) =
  (* We have a system of the form Ax' = Bx, we need one of the form Ax' =
     B'Ax.  If we can factor B = B'A, we're done.  Otherwise, we compute an
     m-by-n matrix T' with m < n, and continue iterating with the system T'Ax'
     = T'Bx. *)
  let module M = QQMatrix in
  let module V = QQVector in
  let module VS = QQVectorSpace in
  let rec fix mA mB =
    let mS = VS.matrix_of (max_rowspace_projection mA mB) in
    (* Since matrices are sparse, need to account for 0-rows of B -- they
       should always be in the max rowspace projection *)
    let mT' =
      SrkUtil.Int.Set.fold
        (fun i (mT', nb_rows) ->
          if V.is_zero (M.row i mB) then
            let mT' =
              M.add_row nb_rows (V.of_term QQ.one i) mT'
            in
            (mT', nb_rows + 1)
          else
            (mT', nb_rows))
        (M.row_set mA)
        (mS, M.nb_rows mB)
      |> fst
    in
    if M.nb_rows mB = M.nb_rows mS then
      (mA, mB)
    else
      fix (M.mul mT' mA) (M.mul mT' mB)
  in
  let (mA, mB) = fix mA mB in

  (* S is the simulation matrix *)
  let mS = VS.matrix_of (VS.simplify (VS.basis (VS.of_matrix mA))) in
  let mD = (* DA = S *)
    match Linear.divide_right mS mA with
    | Some mD -> mD
    | None -> assert false
  in
  let mT = (* DB = TS *)
    match Linear.divide_right (M.mul mD mB) mS with
    | Some mT -> mT
    | None -> assert false
  in
  (* We now have S and T such that Ax' = Bx |= Sx' = TSx, and S has
       full rank.  Now, we need to find a guard; i.e., a basis for the
       space G = { g : Ax' = Bx |= gSx = 0 }. *)
  let dims =
    SrkUtil.Int.Set.elements
      (SrkUtil.Int.Set.union (M.row_set mA) (M.row_set mB))
  in
  let mN =
    Linear.nullspace (M.transpose mA) dims (* { n : nA = 0 } *)
    |> VS.matrix_of
  in
  let guard =
    match Linear.divide_right (M.mul mN mB) mS with
    | Some mG ->
       (* 0 = NAx' = NBx = GSx *)
       VS.of_matrix mG
    | None -> assert false
  in
  (PartialLinearMap.make mT guard, mS)

let dlts_inverse_image sim dlts =
  let mA = sim in
  let dynamics =
    QQMatrix.mul (PartialLinearMap.map dlts) sim
  in
  let dim = QQMatrix.nb_rows sim in
  let mB =
    BatList.fold_lefti (fun mB i dom_constraint ->
        let dom_constraint = Linear.vector_left_mul dom_constraint sim in
        QQMatrix.add_row (i + dim) dom_constraint mB)
      dynamics
      (PartialLinearMap.guard dlts)
  in
  (mA, mB)

(* Compute best abstraction of a DLTS as a DLTS that satisfies
   spectral conditions. *)
let dlts_abstract_spectral spectral_decomp dlts dim =
  let module PLM = PartialLinearMap in
  let rec fix mA mB = (* Ax' = Bx *)
    let (dlts, mS) = determinize (mA, mB) in
    let dom = snd (PLM.iteration_sequence dlts) in
    (* T agrees with dlts for everything in the invariant domain;
         sends everything orthogonal to the invariant domain to 0. *)
    let mT =
      PLM.map (PLM.make (PLM.map dlts) dom)
    in
    let dims = SrkUtil.Int.Set.elements (QQMatrix.row_set mS) in
    let sd = spectral_decomp mT dims in

    let mP = QQVectorSpace.matrix_of sd in
    let mPS = QQMatrix.mul mP mS in
    let mPTS = BatList.reduce QQMatrix.mul [mP; PLM.map dlts; mS] in
    let mPDS =
      BatList.reduce QQMatrix.mul [mP; QQVectorSpace.matrix_of (PLM.guard dlts); mS]
    in
    if List.length sd = QQMatrix.nb_rows mS then
      let map = match Linear.divide_right mPTS mPS with
        | Some t -> t
        | None -> assert false
      in
      let guard = match Linear.divide_right mPDS mPS with
        | Some mG -> QQVectorSpace.of_matrix mG
        | None -> assert false
      in
      (PLM.make map guard, mPS)
    else
      let mB =
        let size = QQMatrix.nb_rows mPS in
        BatEnum.fold (fun m (i, row) ->
            QQMatrix.add_row (i + size) row m)
          mPTS
          (QQMatrix.rowsi mPDS)
      in
      fix mPS mB
  in
  (* DLTS: x' = Tx when Dx = 0; represent in the form Ax' = Bx as
      [ I ] x' = [ T ] x
      [ 0 ]      [ D ]
  *)
  let mA =
    QQMatrix.identity (BatList.of_enum (0 -- (dim - 1)))
  in
  let mB =
    BatList.fold_lefti (fun m i row ->
        QQMatrix.add_row (i + dim) row m)
      (PLM.map dlts)
      (PLM.guard dlts)
  in
  fix mA mB

let periodic_rational_spectrum_reflection dlts dim =
  let spectral_decomp m dims =
    Linear.periodic_rational_spectral_decomposition m dims
    |> List.map (fun (_, _, v) -> v)
  in
  dlts_abstract_spectral spectral_decomp dlts dim

let rational_spectrum_reflection dlts dim =
  let spectral_decomp m dims =
    Linear.rational_spectral_decomposition m dims
    |> List.map (fun (_, v) -> v)
  in
  dlts_abstract_spectral spectral_decomp dlts dim

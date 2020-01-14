open Linear
open Printf

module VS = QQVectorSpace

type kind = Commute | Reset | Ignore

type phased_segment = {
  sim1 : QQMatrix.t;
  sim2 : QQMatrix.t;
  phase1 : QQMatrix.t array;
  phase2 : (kind * QQMatrix.t) array
}

type phased_segmentation = phased_segment list


let commuting_space mA mB =
  let dims = SrkUtil.Int.Set.elements (QQMatrix.row_set mA) in
  let mAB = QQMatrix.mul mA mB in
  let mBA = QQMatrix.mul mB mA in
  let mC = QQMatrix.add mAB (QQMatrix.scalar_mul (QQ.negate QQ.one) mBA) in
  nullspace (QQMatrix.transpose mC) dims

let intersect_rowspaces matrices =
  if Array.length matrices == 0 then
    raise (Invalid_argument "list of matrices should not be empty")
  else
    Array.fold_left 
      (fun mA mB -> 
        let (mC, _) = intersect_rowspace mA mB in
        QQMatrix.mul mC mA)
      (Array.get matrices 0)
      matrices

let vspace_equal mA mB =
  VS.equal (VS.of_matrix mA) (VS.of_matrix mB)

let commuting_segment matrices =
  let pairs = BatArray.cartesian_product matrices matrices in
  let cspaces = Array.map (fun (mA, mB) -> VS.matrix_of (commuting_space mA mB)) pairs in
  let mS = intersect_rowspaces cspaces in
  let rec fix mS =
    let maxlds = Array.map (fun mat -> max_lds mS (QQMatrix.mul mS mat)) matrices in
    let sims, matr = BatArray.split maxlds in
    let mSS = intersect_rowspaces 
                (Array.map (fun m -> QQMatrix.mul m mS) sims)
    in
    if vspace_equal mS mSS then
      mS, matr
    else
      fix mSS
  in
  fix mS

let iter_all = Seq.map (fun (_, m) -> m)

let iter_reset = Seq.filter_map (fun (k, m) -> if k == Reset then Some m else None)

let iter_commute = Seq.filter_map (fun (k, m) -> if k == Commute then Some m else None)


module PhasedSegment = struct

  type t = phased_segment

  (* TODO: find proper representation *)
  let show p = QQMatrix.show p.sim1

  let equal p q =
    QQMatrix.equal p.sim1 q.sim1 &&
    QQMatrix.equal p.sim2 q.sim2 &&
    BatArray.for_all2
      QQMatrix.equal
      p.phase1
      q.phase1 &&
    BatArray.for_all2
      (fun (k1, m1) (k2, m2) -> k1 == k2 && QQMatrix.equal m1 m2)
      p.phase2
      q.phase2

  let make pairs =
    let mS, phase1 = commuting_segment (Array.of_seq (iter_all (Array.to_seq pairs))) in
    let mT, _ = commuting_segment (Array.of_seq (iter_commute (Array.to_seq pairs))) in
    let rec fix mT =
      let ls_maxlds = Array.map
        (fun (k, m) ->
          if k == Reset then
            max_lds ~zero_rows:true mS (QQMatrix.mul mT m)
          else if k == Commute then
            max_lds mT (QQMatrix.mul mT m)
          else
            mT, m
          )
        pairs
      in
      let mTT = intersect_rowspaces
                  (Array.map (fun (m, _) -> QQMatrix.mul m mT) ls_maxlds)
      in
      if vspace_equal mT mTT then
        let phase2 = Array.mapi
                      (fun i (_, m) -> let k, _ = Array.get pairs i in (k, m))
                      ls_maxlds
        in
        { sim1 = mS;
          sim2 = mTT;
          phase1 = phase1;
          phase2 = phase2 }
      else
        fix mTT
    in
    fix mT

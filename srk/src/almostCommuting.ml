open Linear
open Printf

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
  nullspace mC dims

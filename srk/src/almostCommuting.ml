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
  match matrices with
  | [] -> raise (Invalid_argument "list of matrices should not be empty")
  | [m] -> m
  | m :: tail -> List.fold_left 
                  (fun mA mB -> 
                    let (mC, _) = intersect_rowspace mA mB in
                    QQMatrix.mul mC mA)
                  m
                  tail

let vspace_equal mA mB =
  VS.equal (VS.of_matrix mA) (VS.of_matrix mB)

let commuting_segment matrices =
  let pairs = BatList.cartesian_product matrices matrices in
  let cspaces = List.map (fun (mA, mB) -> VS.matrix_of (commuting_space mA mB)) pairs in
  let mS = intersect_rowspaces cspaces in
  let rec fix mS matrices =
    let maxlds = List.map (fun mat -> max_lds mS (QQMatrix.mul mS mat)) matrices in
    let sims, matr = List.split maxlds in
    let mSS = intersect_rowspaces 
                (List.map (fun m -> QQMatrix.mul m mS) sims)
    in
    if vspace_equal mS mSS then
      mS, matr
    else
      fix mSS matrices
  in
  fix mS matrices

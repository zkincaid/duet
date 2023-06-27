open BatPervasives

module I = Polynomial.Rewrite
module V = Linear.QQVector
module QQMatrix = Linear.QQMatrix
module QQXs = Polynomial.QQXs
module Monomial = Polynomial.Monomial
module PLM = Lts.PartialLinearMap

include Log.Make(struct let name = "Srk.TransitionIdeal" end)

(* Transition ideals.  Variables in [0 .. dim -1] correspond to pre-state
   variables, and variables in [ dim .. 2*dim - 1] correspond to post-state
   variables. *)
type t =
  { dim : int
  ; ideal : I.t }

type polynomial_map = QQXs.t array

let compose_polynomial_map f g = Array.map (QQXs.substitute (Array.get g)) f

let make dim ideal = { dim; ideal }

let equal ti1 ti2 =
  ti1.dim = ti2.dim && (I.equal ti1.ideal ti2.ideal)

let pp pp_dim formatter ti =
  let pp_dim' formatter i =
    if i = 2*ti.dim then Format.fprintf formatter "K"
    else if i < ti.dim then pp_dim formatter i
    else Format.fprintf formatter "%a'" pp_dim (i - ti.dim)
  in
  I.pp pp_dim' formatter ti.ideal

(* Matrix-polynomial vector multiplication.  Assumes that the columns of m are
   a subset of {0,...,|polyvec|-1}. *)
let matrix_polyvec_mul m polyvec =
  Array.init (QQMatrix.nb_rows m) (fun i ->
      BatEnum.fold (fun p (coeff, j) ->
          QQXs.add p (QQXs.scalar_mul coeff polyvec.(j)))
        QQXs.zero
        (V.enum (QQMatrix.row i m)))

let compose ti1 ti2 =
  if ti1.dim != ti2.dim then
    invalid_arg "Cannot compose transition ideals of unequal dimension";
  let dim = ti1.dim in
  let a_shift =
    I.generators ti1.ideal
    |> List.map (QQXs.substitute (fun x ->
        if x < dim then QQXs.of_dim (x + 2*dim)
        else QQXs.of_dim x))
  in
  let b_shift =
    I.generators ti2.ideal
    |> List.map (QQXs.substitute (fun x ->
        if x >= dim then QQXs.of_dim (x + dim)
        else QQXs.of_dim x))
  in
  let elim_ord =
    Monomial.block
      [(fun x -> x >= 2 * dim); (fun x -> x >= dim)]
      Monomial.degrevlex
  in
  let ideal = 
    I.mk_rewrite elim_ord (a_shift@b_shift)
    |> I.grobner_basis
    |> I.restrict (fun m ->
        BatEnum.for_all (fun (d, _) -> d < 2 * dim) (Monomial.enum m))
  in
  { dim; ideal }

let domain t =
  let elim_ord =
    Monomial.block [(fun x -> x >= t.dim)] Monomial.degrevlex
  in
  let prestate m =
    BatEnum.for_all (fun (d, _) -> d < t.dim) (Monomial.enum m)
  in
  I.restrict prestate (I.reorder_groebner elim_ord t.ideal)

let invariant_domain t =
  let elim_ord =
    Monomial.block [(fun x -> x >= t.dim)] Monomial.degrevlex
  in
  let postify =
    QQXs.substitute (fun x -> QQXs.of_dim (x + t.dim))
  in
  let prestate m =
    BatEnum.for_all (fun (d, _) -> d < t.dim) (Monomial.enum m)
  in
  let rec loop dom transition_ideal =
    if dom = [] then
      I.restrict prestate transition_ideal
    else
      let transition_ideal' =
        List.fold_left (fun ti p ->
            I.add_saturate ti (postify p))
          transition_ideal
          dom
      in
      let dom' =
        List.filter (fun p ->
            not (QQXs.equal (I.reduce transition_ideal p) QQXs.zero))
          (I.generators (I.restrict prestate transition_ideal'))
      in
      loop dom' transition_ideal'
  in
  let transition_ideal = I.reorder_groebner elim_ord t.ideal in
  loop (I.generators (I.restrict prestate transition_ideal)) transition_ideal

let iteration_sequence t =
  let elim_ord =
    Monomial.block
      [(fun x -> x >= 2 * t.dim); (fun x -> x >= t.dim)]
      Monomial.degrevlex
  in
  let shift_left =
    I.generators t.ideal
    |> List.map (QQXs.substitute (fun x ->
        if x < t.dim then QQXs.of_dim (x + 2*t.dim)
        else QQXs.of_dim x))
  in
  let prestate m =
    BatEnum.for_all (fun (d, _) -> d < t.dim) (Monomial.enum m)
  in
  let transition m =
    BatEnum.for_all (fun (d, _) -> d < 2*t.dim) (Monomial.enum m)
  in
  let rec fix it =
    let shift_right =
      I.generators it.ideal
      |> List.map (QQXs.substitute (fun x ->
          if x >= t.dim then QQXs.of_dim (x + t.dim)
          else QQXs.of_dim x))
    in
    let ideal' =
      List.fold_left (fun rewrite p ->
          I.add_saturate rewrite p)
        (I.mk_rewrite elim_ord shift_right)
        shift_left
      |> I.restrict transition
    in
    let dom = I.restrict prestate ideal' in
    if I.subset dom it.ideal then
      ([it], dom)
    else
      let (seq, stable) = fix { dim = t.dim; ideal = ideal' } in
      (it::seq, stable)
  in
  fix t

(* Are most coefficients of a vector negative? *)
let is_vector_negative vec =
  let sign =
    BatEnum.fold (fun sign (coeff,_) ->
        if QQ.lt coeff QQ.zero then sign - 1
        else sign + 1)
      0
      (V.enum vec)
  in
  sign < 0

let inverse_image ti map =
  let dom_dim = Array.length map in
  (* Shift transition ideal to auxiliary vocabulary
       [2*dom_dim .. 2*dom_dim + 2*dim - 1] 
     Then we add on the polynomials
       x_i - p_i(x_{2*dom_dim},...,x_{2*dom_dim+dim-1})
       x_{i+dom_dim} - p_i(x_{2*dom_dim+dim},...,x_{2*dom_dim+2*dim-1}
     and eliminate the auxiliary vocabulary.
  *)
  let elim_ord =
    Monomial.block
      [(fun x -> x >= 2 * dom_dim)]
      (I.get_monomial_ordering ti.ideal)
  in
  (* Shift into auxiliary [2 * dom_dim ... 2 * dom_dim + 2*dim - 1] vocab *)
  let shift =
    QQXs.substitute (fun x -> QQXs.of_dim (x + 2 * dom_dim))
  in
  (* Shift into post-state of auxiliary vocabulary *)
  let shift_post =
    QQXs.substitute (fun x -> QQXs.of_dim (x + 2 * dom_dim + ti.dim))
  in
  let translation_ideal =
    BatArray.fold_lefti (fun ideal i p ->
        let pre_tr = QQXs.sub (QQXs.of_dim i) (shift p) in
        let post_tr = QQXs.sub (QQXs.of_dim (i + dom_dim)) (shift_post p) in
        I.add_saturate (I.add_saturate ideal pre_tr) post_tr)
      (* Shifted Groebner basis is already a Groebner basis w.r.t. the order
         defined by elim. *)
      (I.mk_rewrite elim_ord (List.map shift (I.generators ti.ideal)))
      map
  in
  let in_target m =
    BatEnum.for_all (fun (d, _) -> d < 2 * dom_dim) (Monomial.enum m)
  in
  { dim = dom_dim 
  ; ideal = I.restrict in_target translation_ideal }

let image ti map dim =
  let post_map =
    Array.map (QQXs.substitute (fun i -> QQXs.of_dim (i + dim))) map
  in
  let inv_image =
    QQXs.substitute (fun i ->
        if i < ti.dim then map.(i)
        else post_map.(i - ti.dim))
  in
  let ideal =
    I.mk_rewrite Monomial.degrevlex (List.map inv_image (I.generators ti.ideal))
    |> I.grobner_basis
  in
  { dim; ideal }

let of_tf_polynomials polynomials tr_symbols =
  let dim = List.length tr_symbols in
  let shift i =
    if i < 0 then QQXs.of_dim i
    else QQXs.of_dim (i + (2 * dim))
  in
  let tr m =
    BatEnum.for_all (fun (d, _) -> d < 2*dim) (Monomial.enum m)
  in
  let elim_ord =
    Monomial.block [(fun x -> x >= 2 * dim)] Monomial.degrevlex
  in
  let eq i p = QQXs.add_term (QQ.of_int (-1)) (Monomial.singleton i 1) p in
  let ideal =
    BatList.fold_lefti (fun defs i (s,s') ->
        let pre = eq i (shift (Syntax.int_of_symbol s)) in
        let post = eq (i + dim) (shift (Syntax.int_of_symbol s')) in
        pre::post::defs)
      (List.map (QQXs.substitute shift) polynomials)
      tr_symbols
    |> I.mk_rewrite elim_ord
    |> I.restrict tr
  in
  { dim; ideal }

(* Solvable polynomial maps **********************************************************)
  
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

(* Candidate solvable equation *)
type solvable_eq =
  { pre : V.t
  ; post : V.t
  ; add : QQXs.t }

let negate_solvable_eq eq =
  { pre = V.negate eq.pre
  ; post = V.negate eq.post
  ; add = QQXs.negate eq.add }

(* Given a polynomial p(x,x',z) [x occupies dimension 0 .. dim-1, x' occupies
   dim .. 2*dim - 1, and z is the rest], rewrite p = 0 in the form
     ax := bx + q(z)
   (Note: post is translated to the pre vocabulary) *)
let format_as_solvable_eq dim p =
  let enum = QQXs.enum p in
  let rec go eq =
    match BatEnum.get enum with
    | None -> Some eq
    | Some (coeff, m) ->
      match Monomial.destruct_var m with
      | Some d ->
        if d < dim then (* pre-state var *)
          go { eq with pre = V.add_term coeff d eq.pre }
        else if d < 2*dim then (* post-state var *)
          go { eq with post = V.add_term (QQ.negate coeff) (d - dim) eq.post }
        else
          go { eq with add = QQXs.add_term coeff m eq.add }
      | None ->
        let in_sim =
          BatEnum.for_all (fun (d, _) -> d >= 2*dim) (Monomial.enum m)
        in
        if in_sim then
          go { eq with add = QQXs.add_term coeff m eq.add }
        else
          None
  in
  go { pre = V.zero; post = V.zero; add = QQXs.zero }

let _solvable_witness abstract_dlts ti =
  let elim =
    Monomial.block [(fun x -> x < 2*ti.dim)] Monomial.degrevlex
  in
  let generators = I.generators ti.ideal
  in
  (* sim is a simulation from ti to sp
     sp is a solvability witness for previous strata
     Rewrite contains:
        x_{i+2*dim} - sim.(i) for each i
        -ax' + bx + q(x)
  *)
  let extract_stratum worklist rewrite =
    let build (mA, mB, pvc, i, rest) p =
      let p = I.reduce rewrite p in
      (* Rewrite p = 0 as ax' = bx + q(z) *)
      match format_as_solvable_eq ti.dim p with
      | None -> (mA, mB, pvc, i, p::rest)
      | Some eq ->
        if QQXs.is_zero p then
          (mA, mB, pvc, i, rest)
        else
          (* Improve readability by negating pre/post/q if most coefficients in
             pre are negative. *)
          let eq =
            if is_vector_negative eq.pre then negate_solvable_eq eq else eq
          in
          (QQMatrix.add_row i eq.post mA,
           QQMatrix.add_row i eq.pre mB,
           eq.add::pvc,
           i+1,
           p::rest)
    in
    let (mA, mB, pvc, _, rest) =
      List.fold_left build (QQMatrix.zero, QQMatrix.zero, [], 0, []) worklist
    in
    let pvc = List.rev pvc in
    let (dlts, mT) = abstract_dlts (mA, mB) in
    (* Ax' = Bx ==> Tx' = DTx; find S such that SA = T, SB = DT, so that we
       can compute the additive vector of the stratum as S*pvc. *)
    let mS =
      let mD = QQMatrix.mul (PLM.map dlts) mT in
      match Lts.containment_witness (mA,mB) (mT,mD) with
      | Some k -> k
      | None -> assert false
    in
    let mA = mT in
    let mB = PLM.map dlts in
    let add = matrix_polyvec_mul mS (Array.of_list pvc) in
    (* Translate additive vector into the target vocabulary *)
    for i = 0 to (Array.length add) - 1; do
      add.(i) <- QQXs.substitute (fun j -> QQXs.of_dim (j - (2*ti.dim))) add.(i)
    done;
    (mA, mB, add, rest)
  in
  let rec fix worklist sp sim rewrite target_dim =
    let (mA, mB, blk_add, rest) = extract_stratum worklist rewrite in
    let size = Array.length blk_add in
    if size = 0 then
      (sp, sim)
    else
      let blk_transform = QQMatrix.dense_of mB size size in
      let block = { blk_transform; blk_add } in
      let sp = block :: sp in
      let sim = mA :: sim in
      let mBA = QQMatrix.mul mB mA in
      let rewrite =
        BatEnum.fold (fun rewrite i ->
            (* x_{i + target_dim} = sim.(i) *)
            let sim_row = QQXs.of_vec (QQMatrix.row i mA) in
            let p = 
              QQXs.add_term
                (QQ.of_int (-1))
                (Monomial.singleton (target_dim + i) 1)
                sim_row
            in
            let post_neg_sim =
              QQXs.substitute (fun j -> QQXs.negate (QQXs.of_dim (j + ti.dim))) sim_row
            in
            let q = 
              QQXs.add
                post_neg_sim
                (QQXs.add
                   (QQXs.of_vec (QQMatrix.row i mBA))
                   (QQXs.substitute
                      (fun j -> QQXs.of_dim (j + (2*ti.dim)))
                      blk_add.(i)))
            in
            I.add_saturate (I.add_saturate rewrite p) q)
          rewrite
          (0 -- (size - 1))
      in
      fix rest sp sim rewrite (target_dim + size)
  in
  let (witness, sim) = 
    fix generators [] [] (I.mk_rewrite elim []) (2*ti.dim)
  in
  let size =
    List.fold_left (fun size sim -> size + (QQMatrix.nb_rows sim)) 0 sim
  in
  let flat_sim = Array.make size QQXs.zero in
  let rec populate = function
    | [] -> 0
    | (x::xs) ->
      let index = populate xs in
      BatEnum.iter
        (fun (i, row) ->
           flat_sim.(i + index) <- QQXs.of_vec row)
        (QQMatrix.rowsi x);
      (index + (QQMatrix.nb_rows x))
  in
  ignore (populate sim);
  (List.rev witness, flat_sim)

let solvable_witness = _solvable_witness Lts.determinize

let periodic_rational_solvable_witness =
  let abstract_dlts (mA, mB) =
    let (dlts, mD) = Lts.determinize (mA, mB) in
    let (dlts, mP) =
      Lts.periodic_rational_spectrum_reflection dlts (QQMatrix.nb_rows mD)
    in
    (dlts, QQMatrix.mul mP mD)
  in
  _solvable_witness abstract_dlts

let solvable_reflection ti =
  let (witness, sim) = solvable_witness ti in
  (inverse_image ti sim, sim, witness)


let ultimately_solvable_reflection ti =
  let rec loop sim ti =
    let dom = invariant_domain ti in
    let ti_dom =
      { ti with ideal = List.fold_left I.add_saturate ti.ideal (I.generators dom) }
    in
    let (witness, sim') = solvable_witness ti_dom in
    let ti' = inverse_image ti sim' in
    if ti.dim = ti'.dim then
      (ti', compose_polynomial_map sim' sim, witness)
    else
      loop (compose_polynomial_map sim' sim) ti'
  in
  let id = Array.init ti.dim (fun i -> QQXs.of_dim i) in
  loop id ti




(** Produce a formatted string representing the matrix recurrence *)
let pp_mat_rec f (matrix, offset, add) = 
  let primed_str = Array.init (Array.length matrix) (fun i -> "x_" ^ (string_of_int (i+offset)) ^ "'") in
  let unprimed_str = Array.init (Array.length matrix) (fun i -> "x_" ^ (string_of_int (i+offset))) in
  let add_str = Array.map (SrkUtil.mk_show (QQXs.pp (fun fo d -> Format.fprintf fo "x_%d" d))) add in
  let matrix_str = Array.map (fun x -> Array.map QQ.show x) matrix in
  let length_of_biggest_primed = Array.fold_left (fun a b -> max a (String.length b)) 0 primed_str in
  let length_of_biggest_unprimed = Array.fold_left (fun a b -> max a (String.length b)) 0 unprimed_str in
  let length_of_biggest_add = Array.fold_left (fun a b -> max a (String.length b)) 0 add_str in
  let lens_with_format_list = 
    List.init (Array.length matrix) (
      fun i ->
        let len = Array.fold_left (
          fun maxi r ->
            max maxi (String.length r.(i))
            ) (-1) matrix_str in
        Scanf.format_from_string ("%" ^ (string_of_int (len+1)) ^ "s") "%s"
    ) in
  let primed_form = Scanf.format_from_string ("| %" ^ string_of_int length_of_biggest_primed ^ "s |") "%s" in
  let unprimed_form = Scanf.format_from_string ("| %" ^ string_of_int length_of_biggest_unprimed ^ "s |") "%s" in
  let add_form = Scanf.format_from_string ("| %" ^ string_of_int length_of_biggest_add ^ "s |") "%s" in
  let pp_row f i = 
    Format.pp_open_box f 0;
    Format.fprintf f primed_form primed_str.(i);
    if i = ((Array.length matrix_str)/2) then
      Format.fprintf f "%3s" " = "
    else
      Format.fprintf f "%3s" "";
    let row_lis = Array.to_list (Array.get matrix_str i) in
    Format.pp_print_string f "|";
    List.iter2 (fun form value -> Format.fprintf f form value) lens_with_format_list row_lis;
    Format.pp_print_string f " |";
    if i = ((Array.length matrix_str)/2) then
      Format.fprintf f "%3s" " * "
    else
      Format.fprintf f "%3s" "";
    Format.fprintf f unprimed_form unprimed_str.(i);
    if i = ((Array.length matrix_str)/2) then
      Format.fprintf f "%3s" " + "
    else
      Format.fprintf f "%3s" "";
    Format.fprintf f add_form add_str.(i);
    Format.pp_close_box f ();
    Format.pp_print_space f ()
  in
  Format.pp_open_vbox f 0;
  Array.iteri (fun i _ -> pp_row f i) matrix;
  Format.pp_print_newline f ();
  Format.pp_close_box f ()

let pp_sp f sp = 
  let _ = List.fold_left (
    fun (i, offset) (blk : block) ->
      Format.fprintf f "@[Block %d : %a@]" i pp_mat_rec (blk.blk_transform, offset, blk.blk_add);
      (i+1, offset + (Array.length blk.blk_transform))      
      ) (1, 0) sp in
  ()
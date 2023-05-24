module L =  Log.Make(struct let name = "srk.order" end)

open Normalizffi

module MakeOrder(A : sig
    val rank : int
    val mult : int -> int -> ZZ.t array

  end) = struct

  module ZZV = Ring.MakeVector(ZZ)
  module ZZM = Ring.MakeMatrix(ZZ)

  let zzmify = ZZM.of_dense

  let unzzmify matrix = 
    ZZM.dense_of matrix (ZZM.nb_rows matrix) (ZZM.nb_columns matrix)


  let mult_table = 
    let m = Array.make (A.rank * A.rank) (Array.make A.rank ZZ.zero) in
    for i = 0 to A.rank - 1 do
      for j = 0 to A.rank - 1 do
        m.(i * A.rank + j) <- A.mult i j
      done
    done;
    zzmify m

  type pre_ideal = Red of ZZM.t | UnRed of ZZM.t

  type ideal = pre_ideal ref

  type elem = ZZ.t array

  let get_mat i = match !i with Red m | UnRed m -> m

  let idealify aa = 
    ref (UnRed (zzmify aa))


  let dense_hermite_normal_form matrix =
    let level = `trace in
    let verbose = Log.level_leq (!L.my_verbosity_level) level in
    if verbose then Flint.set_debug true else ();
    let mat = Flint.new_matrix matrix in
    Flint.hermitize mat;
    let rank = Flint.rank mat in
    let basis =
      Flint.denom_matrix_of_rational_matrix mat
      |> snd
      |> BatList.take rank (* The rows after rank should be all zeros *)
    in
    if verbose then Flint.set_debug false;
    basis

  let hermite_normal_form mat = 
    let matrix = Array.to_list (Array.map (fun r -> Array.to_list (Array.map ZZ.mpz_of r)) (unzzmify mat)) in
    let m = ZZM.nb_rows mat in
    let n = ZZM.nb_columns mat in
    let mapper i row = 
      let pad = List.init m (fun j -> if i = j then Mpzf.of_int 1 else Mpzf.of_int 0) in
      row @ pad
    in
    let hu = dense_hermite_normal_form (List.mapi mapper matrix) in
    let splitter hurow = 
      let rec aux i prev rest = 
        if i >= n then
          Array.of_list (List.rev prev), Array.of_list (List.map ZZ.of_mpz rest)
        else
          match rest with
          | [] -> failwith "Didn't find u matrix?"
          | x :: xs -> aux (i+1) (ZZ.of_mpz x :: prev) xs
      in
      aux 0 [] hurow
    in
    let h, u = Array.split (Array.of_list (List.map splitter hu)) in
    zzmify h, zzmify u

  let get_reduced i = 
    match !i with 
    | Red m -> m 
    | UnRed m -> 
      let red = fst (hermite_normal_form m) in
      i := Red red;
      red

  let stack a b =
    let am = ZZM.nb_rows a in
    let brs = ZZM.rowsi b in
    BatEnum.fold (fun acc (i, brow) -> ZZM.add_row (i+am) brow acc) a brs

  let kronecker a b = 
    let am, an = ZZM.nb_rows a, ZZM.nb_columns a in
    let bm, bn = ZZM.nb_rows b, ZZM.nb_columns b in
    let aa, ba = unzzmify a, unzzmify b in
    let m = Array.make_matrix (am * bm) (an * bn) ZZ.zero in
    for i = 0 to am * an - 1 do
      for j = 0 to bm * bn - 1 do
        m.(i).(j) <- ZZ.mul aa.(i / bm).(j / bn) ba.(i mod bm).(j mod bn)
      done
    done;
    zzmify m



  let get_smallest_int i = 
    ZZM.entry (A.rank - 1) (A.rank - 1) (get_reduced i)

  let pp_i f i = 
    ZZM.pp ZZ.pp f (get_reduced i)

  let equal_i a b = 
    ZZM.equal (get_reduced a) (get_reduced b)


  let sum_i a b =
    ref (UnRed (stack (get_mat a) (get_mat b)))

  let mul_i a b = 
    ref (UnRed (ZZM.mul (kronecker (get_reduced a) (get_reduced b)) mult_table))

  let mul_v_by_basis_v v basis_i = 
    fst (Array.fold_left (
      fun (acc, j) vj ->
        let x = Array.map (fun y -> ZZ.mul vj y) (A.mult basis_i j) in
        Array.map2 ZZ.add acc x, j+1
    ) (Array.make A.rank ZZ.zero, 0) v)

  let ideal_generated_by a = 
    let m = Array.make A.rank (Array.make A.rank ZZ.zero) in
    for i = 0 to A.rank - 1 do
      m.(i) <- mul_v_by_basis_v a i
    done;
    ref (UnRed (zzmify m))

  let one_i = ref (Red (ZZM.identity (List.init A.rank (fun i -> i))))


  let get_lower_left_corner a = 
    let m = ZZM.nb_rows a in
    let aa = unzzmify a in
    let r = Array.make_matrix A.rank A.rank ZZ.zero in
    for i = 0 to A.rank - 1 do
      r.(i) <- Array.sub (aa.(i + (m-A.rank))) 0 A.rank
    done;
    zzmify r


  let intersect_i a b = 
    let a_red, b_red = get_reduced a, get_reduced b in
    let (_, u) = hermite_normal_form (stack a_red b_red) in
    let u_sub = get_lower_left_corner u in
    ref (UnRed (ZZM.mul u_sub a_red))

  
  let quotient_i a b = 
    let ba = unzzmify (get_reduced b) in
    let neg_aa = unzzmify (ZZM.scalar_mul (ZZ.of_int (-1)) (get_reduced a)) in
    let top_part = Array.of_list (List.init A.rank (
      fun i ->
        Array.concat (List.init A.rank (
          fun j ->
            mul_v_by_basis_v ba.(j) i
        ))
    )) in
    let bot_part = Array.concat (List.init A.rank (
      fun i ->
        let r = List.init A.rank (
          fun j ->
            if i = j then neg_aa
            else Array.make_matrix A.rank A.rank ZZ.zero
        ) in
        List.fold_left (
          fun acc sr ->
            Array.map2 Array.append acc sr
        ) (List.hd r) (List.tl r)
    )) in
    let (_, u) = hermite_normal_form (stack (zzmify top_part) (zzmify bot_part)) in
    ref (UnRed (get_lower_left_corner u))


  let get_matrix_gcd i = 
    BatEnum.fold (
      fun g (_, _, e) -> ZZ.gcd g e) ZZ.zero (ZZM.entries (get_reduced i))

  let scalar_mul_i a i =
    match !i with
    | UnRed m -> ref (UnRed (ZZM.scalar_mul a m))
    | Red m -> ref (Red (ZZM.scalar_mul a m))

  let divide_common_factor common_factor i = 
    match !i with
    | Red m ->
      ref (Red (ZZM.map_rows (
        fun r ->
          ZZV.map (fun _ e -> ZZ.div e common_factor) r
      ) m))
    | UnRed m ->
      ref (UnRed (ZZM.map_rows (
        fun r ->
          ZZV.map (fun _ e -> ZZ.div e common_factor) r
      ) m))

  type pre_frac_ideal = Norm of ZZ.t * ideal | UnNorm of ZZ.t * ideal

  type frac_ideal = pre_frac_ideal ref


  let one = ref (Norm (ZZ.one, one_i))

  let get_normalized (i : frac_ideal) = 
    match !i with
    | Norm (d, a) -> (d, a)
    | UnNorm (d, a) ->
      let matrix_factor = get_matrix_gcd a in
      let common_factor = ZZ.gcd d matrix_factor in
      if ZZ.equal common_factor ZZ.one then 
        (i := Norm (d, a);
        d, a)
      else
        (let new_d, new_a = ZZ.div d common_factor, divide_common_factor common_factor a in
        i := Norm (new_d, new_a);
        new_d, new_a)

  let get_den_and_ideal (i : frac_ideal) = 
    match !i with | Norm (d, id) | UnNorm (d, id) -> (d, id)

  let sum ai bi = 
    let (d1, a) = get_den_and_ideal ai in
    let (d2, b) = get_den_and_ideal bi in
    let new_d = ZZ.lcm d1 d2 in
    ref (UnNorm (new_d, sum_i (scalar_mul_i (ZZ.div new_d d1) a) (scalar_mul_i (ZZ.div new_d d2) b)))

  let intersect ai bi = 
    let (d1, a) = get_den_and_ideal ai in
    let (d2, b) = get_den_and_ideal bi in
    let new_d = ZZ.lcm d1 d2 in
    new_d, intersect_i (scalar_mul_i (ZZ.div new_d d1) a) (scalar_mul_i (ZZ.div new_d d2) b)

  let mul ai bi = 
    match !ai, !bi with
    | Norm (d1, a), Norm (d2, b) -> ref (Norm ((ZZ.mul d1 d2), mul_i a b))
    | Norm(d1, a), UnNorm(d2, b) | UnNorm(d1, a), Norm(d2, b) | UnNorm(d1, a), UnNorm(d2, b) -> ref (UnNorm (ZZ.mul d1 d2, mul_i a b))

  let exp i ai = 
    let rec aux acc j = 
      if j = 0 then acc
      else
        aux (mul ai acc) (j-1)
      in
    aux one i


  let quotient ai bi = 
    let (d1, a) = get_den_and_ideal ai in
    let (d2, b) = get_den_and_ideal bi in
    let smallest_int = get_smallest_int b in
    let new_d = ZZ.mul d1 smallest_int in
    let new_m = quotient_i (scalar_mul_i (ZZ.mul d2 smallest_int) a) b in
    ref (UnNorm (new_d, new_m))

  let pp f i = 
    let (d, a) = get_normalized i in
    Format.fprintf f "@[1/(%a)@]" ZZ.pp d;
    pp_i f a
  
  let equal ai bi = 
    let (d1, a) = get_normalized ai in
    let (d2, b) = get_normalized bi in
    ZZ.equal d1 d2 && equal_i a b

  let subset a b = 
    equal b (sum a b)

  let make_frac_ideal d i = 
    ref (UnNorm (d, i))


  let compute_overorder o i = 
    let rec aux c j =
      let c_div_j = quotient c j in
      let x = quotient c_div_j c_div_j in
      if equal x c then (c, j)
      else aux x (mul c j)
    in
    aux o i

  module IM = SrkUtil.Int.Map

  let factor_refinement is = 
    let init_c = List.fold_left (fun acc i -> fst (compute_overorder acc i)) one is in
    let js = List.map (fun i -> mul i init_c, 1) is in
    let rec aux next_index worklist c l = 
      match worklist with
      | [] -> c, l
      | (m, n) :: rest ->
        let (jm, jme), (jn, jne) = IM.find m l, IM.find n l in
        let h = sum jm jn in
        if equal c h then aux next_index rest c l
        else
          let new_c, h = compute_overorder c h in
          let new_worklist = List.filter (fun (a, b) -> a <> m && a <> n && b <> m && b <> n) worklist in
          let new_l = IM.remove m (IM.remove n l) in
          let new_l = IM.map (fun (j, e) -> mul j new_c, e) new_l in
          let jmp = quotient jm h in
          let jnp = quotient jn h in
          let active_indices = IM.keys new_l in
          let new_worklist, new_l, next_index, active_indices = 
            if not (equal jmp new_c) then
              let new_l = IM.add next_index (jmp, jme) new_l in
              let new_pairs = BatEnum.map (fun i -> (i, next_index)) active_indices in
              (new_worklist @ (BatList.of_enum new_pairs), new_l, next_index + 1, BatEnum.icons next_index active_indices)
            else
              new_worklist, new_l, next_index, active_indices
          in
          let new_worklist, new_l, next_index, active_indices = 
            if not (equal jnp new_c) then
              let new_l = IM.add next_index (jnp, jne) new_l in
              let new_pairs = BatEnum.map (fun i -> (i, next_index)) active_indices in
              (new_worklist @ (BatList.of_enum new_pairs), new_l, next_index + 1, BatEnum.icons next_index active_indices)
            else
              new_worklist, new_l, next_index, active_indices
          in
          let new_l = IM.add next_index (h, jme + jne) new_l in
          let new_pairs = BatEnum.map (fun i -> (i, next_index)) active_indices in
          let new_worklist = new_worklist @ (BatList.of_enum new_pairs) in
          aux (next_index + 1) new_worklist new_c new_l
    in
    let indices = List.mapi (fun i _ -> i) js in
    let next_index = List.length js in
    let l = List.fold_left (fun l i -> IM.add i (List.nth js i) l) IM.empty indices in
    let get_pairs l = List.filter (fun (x, y) -> x<>y) (fst(List.fold_left (fun (acc, l1) x -> (acc @ (List.map (fun y -> (x, y)) l1),List.tl l1)) ([],l) l)) in
    let c, gcd_basis = aux next_index (get_pairs indices) init_c l in
    c, BatList.of_enum (IM.values gcd_basis)

  let compute_factorization is = 
    let over, gcd_basis = factor_refinement is in
    let is = List.map (fun i -> mul over i) is in
    List.map (
      fun i ->
        let fact_list, _ = 
          List.fold_left (
            fun (flist, curr_h) (j, _) ->
              let rec aux h fj = 
                if subset h j then
                  aux (quotient h j) (fj + 1)
                else
                  fj :: flist, h
              in
              aux curr_h 0
          ) ([], i) gcd_basis in
        List.rev fact_list
    ) is, fst (List.split gcd_basis), over

  let find_unit_basis l = 
    let is = List.map (fun a -> make_frac_ideal ZZ.one (ideal_generated_by a)) l in
    let exps, _, _ = compute_factorization is in
    let exps_m = zzmify (
      Array.of_list (
        List.map (
          fun r ->
            Array.of_list (List.map ZZ.of_int r)
        ) exps        
      )) in
    let (h, u) = hermite_normal_form exps_m in
    let h_size = ZZM.nb_rows h in
    let basis_size = (ZZM.nb_rows exps_m) - h_size in
    let indices_to_grab = List.init basis_size (fun i -> h_size + i) in
    List.map (
      fun i ->
        let r = ZZM.row i u in
        let int_rows = BatEnum.map (
          fun (c, _) ->
            match ZZ.to_int c with
            | None -> failwith "Exponent overflow"
            | Some i -> i
        ) (ZZV.enum r) in
        BatList.of_enum int_rows
    ) indices_to_grab

end

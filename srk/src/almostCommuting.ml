open Linear
open BatPervasives 

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

let intersect_rowspaces matrices dims =
  Array.fold_left 
    (fun mA mB -> 
      let (mC, _) = intersect_rowspace mA mB in
      QQMatrix.mul mC mA)
    (QQMatrix.identity dims)
    matrices

let rowspace_equal mA mB =
  VS.equal (VS.of_matrix mA) (VS.of_matrix mB)

let commuting_segment matrices dims =
  let pairs = BatArray.cartesian_product matrices matrices in
  let cspaces = Array.map (fun (mA, mB) -> VS.matrix_of (commuting_space mA mB)) pairs in
  let mS = intersect_rowspaces cspaces dims in
  let rec fix mS =
    let maxlds = Array.map (fun mat -> max_lds mS (QQMatrix.mul mS mat)) matrices in
    let sims, matr = BatArray.split maxlds in
    let mSS = intersect_rowspaces 
                (Array.map (fun m -> QQMatrix.mul m mS) sims)
                dims
    in
    if rowspace_equal mS mSS then
      mS, matr
    else
      fix mSS
  in
  fix mS

let iter_all     = Array.map (fun (_, m) -> m)
let iter_reset   = BatArray.filter_map (fun (k, m) -> if k == Reset then Some m else None)
let iter_commute = BatArray.filter_map (fun (k, m) -> if k == Commute then Some m else None)

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
    if Array.length pairs == 0 then
      raise (Invalid_argument "Array of matrices should not be empty")
    else
      let _, mA = Array.get pairs 0 in
      let dims = BatList.of_enum (0 -- ((QQMatrix.nb_columns mA) - 1)) in
      let mS, phase1 = commuting_segment (iter_all pairs) dims in
      let mT, _ = commuting_segment (iter_commute pairs) dims in
      let maxldss mT =
        Array.map
          (fun (k, m) ->
            if k == Reset then
              let mC, mD = pushout (QQMatrix.mul mT m) mS in
              (* pushout TA S returns C,D such that CTA = DS. We then take the
                 rowspace intersection of the matrices CT for all A, and iterate
                 with T' = \bigcap CT. A fixpoint should be reached after two
                 iterations, i.e. we have rsp(T') = rsp(T). If the fixpoint is
                 reached, then there exists a C' s.t. C'CT = T. We use C' to
                 perform a change of basis in order to get TA = C'DS. *)
              match divide_right mT (QQMatrix.mul mC mT) with
              | Some mC' -> mC, (QQMatrix.mul mC' mD)
              | None     -> mC, mD
            else if k == Commute then
              max_lds mT (QQMatrix.mul mT m)
            else
              (QQMatrix.identity dims), m)
          pairs
      in
      let ls = maxldss mT in
      let mk_sim2 mT ls = intersect_rowspaces
                            (Array.map (fun (m, _) -> QQMatrix.mul m mT) ls)
                            dims
      in
      let mT' = mk_sim2 mT ls in
      let ls' = if rowspace_equal mT mT' then ls else maxldss mT' in
      let phase2 = Array.map2 (fun (k, _) (_, m) -> (k, m)) pairs ls' in
      (* Abstraction fixpoint should be reached after at most two steps *)
      assert (rowspace_equal mT' (mk_sim2 mT' ls'));
      { sim1 = mS;
        sim2 = mT';
        phase1 = phase1;
        phase2 = phase2 }

end

module PhasedSegmentation = struct

  type t = phased_segment list

  let make_naive matrices = 
    let len = Array.length matrices in
    let products = BatList.n_cartesian_product (BatList.make len [Commute; Reset]) in
    let partitions = BatList.map 
                       (fun p -> Array.map2 (fun x y -> x, y) (Array.of_list p) matrices) 
                       products
    in
    BatList.map PhasedSegment.make partitions

  let make matrices =
    let segments = BatQueue.create () in
    let current_space = ref VS.empty in
    let push s =
      current_space := VS.sum !current_space (VS.of_matrix s.sim2);
      BatQueue.push s segments
    in
    let set_kind ps i k =
      let ps' = Array.copy ps in
      let _, mM = Array.get ps' i in
      Array.set ps' i (k, mM);
      ps'
    in
    (* Start with a segment where all matrices are non-resets *)
    let pairs = Array.map (fun mM -> (Commute, mM)) matrices in
    push (PhasedSegment.make pairs);
    let rec iter ps seg i =
      (* Only continue if rsp(seg.sim2) is not already contained in the current space *)
      if not (VS.subspace (VS.of_matrix seg.sim2) !current_space) then
        if i >= (Array.length ps) then
          push seg
        else
          let ps' = set_kind ps i Reset in
          let seg' = PhasedSegment.make ps' in
          let ps'' = set_kind ps i Commute in
          let seg'' = PhasedSegment.make ps'' in
          (* It suffices to proceed with only the reset extension if it subsumes the non-reset extension *)
          if (VS.subspace (VS.of_matrix seg''.sim2) (VS.of_matrix seg'.sim2)) then
            iter ps' seg' (i+1)
          else
            iter ps' seg' (i+1);
            iter ps'' seg'' (i+1)
    in
    let pairs = Array.map (fun mM -> (Ignore, mM)) matrices in
    let seg = PhasedSegment.make pairs in
    iter pairs seg 0;
    BatList.of_enum (BatQueue.enum segments)

  let almost_commuting_space segmentation =
    List.fold_left
      (fun vU s -> VS.sum vU (VS.of_matrix s.sim2))
      VS.empty
      segmentation

  let almost_commutes segmentation =
    let vU = almost_commuting_space segmentation in
    let dim = VS.dimension vU in
    VS.equal vU (VS.standard_basis dim)

  let best_almost_commuting matrices =
    let segmentation = make_naive matrices in
    let mC = VS.matrix_of (almost_commuting_space segmentation) in
    mC, (Array.map (fun m -> 
                      match divide_right (QQMatrix.mul mC m) mC with
                      | Some mM -> mM
                      | None -> assert false)
                   matrices)

end

module ACLTS = struct
  module LTS = LinearSemiautomaton
  module E = ExpPolynomial
  open Syntax
  open BatPervasives
  include Log.Make(struct let name = "srk.aclts" end)


  type 'a t = phased_segmentation

  (*TODO:Make a better pp function*)
  let pp srk tr_symbols formatter aclts = 
    Format.fprintf formatter "Printing aclts";
    BatList.iteri (fun ind seg ->
        Format.fprintf formatter "Currently Printing Phase %n \n _________________________ \n" ind;
        Format.fprintf formatter "Sim1 matrix is %a \n" (QQMatrix.pp) seg.sim1;
        Format.fprintf formatter "\n\nPrinting sim1 Arrays: \n";
        BatArray.iteri (fun indmat mat ->
            Format.fprintf formatter "Phase 1 transformer %d is \n %a \n\n" indmat (QQMatrix.pp) mat) seg.phase1;
        Format.fprintf formatter "Sim2 matrix is %a \n" (QQMatrix.pp) seg.sim2;
        Format.fprintf formatter "\n\nPrinting sim2 Arrays: \n";
        BatArray.iteri (fun indmat (kind, mat) ->
            match kind with
            | Reset ->
              Format.fprintf formatter "Phase 2 transformer %d is RESET and is \n %a \n\n" indmat (QQMatrix.pp) mat
            | Commute ->
              Format.fprintf formatter "Phase 2 transformer %d is COMMUTE and is \n %a \n\n" indmat (QQMatrix.pp) mat
            | Ignore ->
              Format.fprintf formatter "Phase 2 transformer %d is IGNORE and is \n %a \n\n" indmat (QQMatrix.pp) mat) 
          seg.phase2) 
      aclts



  let abstract ?(exists=fun x -> true) srk tr_symbols phi =
    Log.errorf "formula is %a" (Formula.pp srk) phi;
    let lts = LTS.abstract ~exists srk phi tr_symbols in
    Log.errorf "LTS sim matrix is %a" (QQMatrix.pp) (LTS.simulation lts);
    BatList.iter (fun transformer ->
        Log.errorf "LTS transformer is %a" (QQMatrix.pp) transformer
      ) (LTS.transitions lts);

    let trans_array = BatArray.of_list (LTS.transitions lts) in
    if BatArray.length trans_array = 0 then []
    else(
      let aclts = PhasedSegmentation.make trans_array in
      let result = BatList.map (fun ph_seg -> 
          {sim1 = QQMatrix.mul ph_seg.sim1 (LTS.simulation lts);
           sim2 = QQMatrix.mul ph_seg.sim2 (LTS.simulation lts);
           phase1 = ph_seg.phase1;
           phase2 = ph_seg.phase2})
          aclts
      in
      result
    )


  let create_sym_map srk tr_symbols =
    List.fold_left
      (fun map (sym, sym') -> Symbol.Map.add sym (mk_const srk sym') map)
      Symbol.Map.empty
      tr_symbols

  let postify srk tr_symbols = substitute_map srk (create_sym_map srk tr_symbols)

  let preify srk tr_symbols = substitute_map srk
      (create_sym_map srk (List.map (fun (x, x') -> (x', x)) tr_symbols))


  (* Here we create a bunch of vars that will be used
   * reachability relation.
   * For each phase, we create vars recording how many times
   * each transition was executed after last reset (trans_exec_vars),
   * on which transformer the last reset occured (reset_transformer_var)
   * and what the value for each row of the ac sim matrix is once the reset occurs
   * (ph2_entrance_vals). We also create exp_vars_summed which is just an
   * optimization; it is a var equal to the sum of trans_exec_vars.
  *)
  let create_exp_vars srk aclts =
    BatList.mapi 
      (fun phase_ind ph_seg ->
         let trans_exec_vars = 
           BatArray.mapi (fun trans_ind transformer ->
               match transformer with
               | Ignore, _ -> failwith "Ignore as kind during create_exp_vars"
               | Reset, _ -> mk_zero srk
               | Commute, _ -> 
                 let name = Format.sprintf "K%d,%d" phase_ind trans_ind in
                 mk_const srk (mk_symbol srk ~name `TyInt))
             ph_seg.phase2
         in
         let reset_transformer_var =
           if BatArray.exists (fun (kind, _) -> kind = Reset) ph_seg.phase2 then
             mk_const srk  (mk_symbol srk ~name:("R"^(string_of_int phase_ind)) `TyInt)
           else
             mk_real srk (QQ.of_int (-1))
         in
         let ph2_entrance_vals =
           BatList.map (fun row -> 
               mk_const srk (mk_symbol srk ~name:(Format.sprintf "S%d,%d" phase_ind row) `TyReal))
             (BatList.of_enum (0 -- (QQMatrix.nb_rows ph_seg.sim2)))
         in
         let exp_vars_summed = 
           mk_const srk (mk_symbol srk ~name:("KSUM"^(string_of_int phase_ind)) `TyInt)
         in
         trans_exec_vars, reset_transformer_var, ph2_entrance_vals, exp_vars_summed
      ) aclts

  let create_global_vars srk aclts =
    BatArray.mapi (fun trans_ind _ ->
        let name = Format.sprintf "M%d" trans_ind in
        mk_const srk (mk_symbol srk ~name `TyInt))
      (List.hd aclts).phase1


  (* Pair each phase segment exp_var *)
  let all_pairs exp_vars =
    let rec helper exp_vars =
      match exp_vars with
      | [] -> []
      | cur_ph_vars :: tl -> 
        (BatList.map (fun ph_exp_vars -> (cur_ph_vars, ph_exp_vars)) tl) ::
        (helper tl)
    in
    List.flatten (helper exp_vars)


  (* If equiv class was never reset (number
   * transitions taken == loop counter),
   * reset var is set to -1 (sentinel value).
  *)
  let exp_reset_never_taken_constr srk exp_vars loop_counter =
    mk_and srk  
      (List.map 
         (fun (trans_exec_vars, res, _, _) -> 
            mk_iff srk
              (mk_eq srk
                 (mk_add srk (BatArray.to_list  trans_exec_vars))
                 loop_counter)
              (mk_eq srk res (mk_real srk (QQ.of_int (-1)))))
         exp_vars)

  (* Create every permutation of phase2 segments *)
  let exp_perm_constraints srk pairs =
    let mk_nat_leq srk x y =
      match Term.destruct srk x, Term.destruct srk y with
      | (`Real k, _) when QQ.equal k QQ.zero -> mk_true srk
      | (_, `Real k) when QQ.equal k QQ.zero -> mk_eq srk x (mk_zero srk)
      | (_, _) -> mk_leq srk x y
    in 
    mk_and srk
      (List.map 
         (fun ((trans_exec1, _, _, _), (trans_exec2, _, _, _)) -> 
            let lessthan k1 k2 = mk_and srk 
                ((BatArray.map2 (fun k1' k2' -> mk_nat_leq srk k1' k2') k1 k2) |> BatArray.to_list)
            in
            mk_or srk [lessthan trans_exec1 trans_exec2;  lessthan trans_exec2 trans_exec1])
         pairs)


  (* If two phase 2 segments have taken
   * the same number of transitions after their last reset, 
   * both segments must've been last reset at same time*)
  let exp_equality_reset_together_constraints srk pairs =
    mk_and srk
      (List.map
         (fun ((_, r1, _, sum1), (_, r2, _, sum2)) ->
            mk_iff srk
              (mk_eq srk
                 sum1
                 sum2)
              (mk_eq srk r1 r2))
         pairs)

  (*Relate the individual #times each trans taken with the sum vars*)
  let exp_connect_sum_constraints srk exp_vars =
    mk_and srk
      (List.map (fun (trans_exec, _, _, sum) ->
           mk_eq srk (mk_add srk (BatArray.to_list trans_exec)) sum)
          exp_vars)

  (* Make input terms each >= 0 *)
  let mk_all_nonnegative srk terms =
    terms
    |> List.map (mk_leq srk (mk_zero srk))
    |> mk_and srk


  let linmatrix_to_term_array srk term_vec matrix size =
    BatEnum.fold
      (fun arr (dim, row) -> arr.(dim)<-Linear.term_of_vec srk term_vec row; arr)
      (BatArray.make size (mk_zero srk))
      (QQMatrix.rowsi matrix)

  let expmatrix_to_term_array srk term_vec matrix exp_term size =
    BatEnum.fold
      (fun arr (dim, row) -> arr.(dim)<-E.term_of_vec srk term_vec exp_term row; arr)
      (BatArray.make size (mk_zero srk))
      (E.Matrix.rowsi matrix)


  let mk_eq_symmaps_LHS srk a1 a2 =
    mk_and srk 
    @@ BatArray.to_list 
    @@ BatArray.mapi
      (fun ind term ->
         Log.errorf "new eq is %a" (Formula.pp srk) (mk_eq srk term a2.(ind));
         mk_eq srk term a2.(ind))
      a1


  (*Uses sx_constraints_helper to set initial values for each dimension of each equiv class*)
  let stateless_last_reset_core_logic_constrs srk tr_symbols aclts exp_vars pairs 
      global_trans =
    mk_and srk
      (List.mapi (fun seg_ind (trans_exec, res, entrance, sum) ->
           let this_seg = (List.nth aclts seg_ind) in
           let res_taken =
             mk_or srk
             @@  BatArray.to_list 
             @@ BatArray.mapi (fun trans_ind (kind, res_trans) ->
                 match kind with
                 | Commute -> mk_false srk
                 | Ignore -> failwith "Ignore made it to exp"
                 | Reset ->
                   let more_recently_reset_phases_constr =
                     BatList.mapi (fun seg2_ind (trans_exec2, _, _, sum2) ->
                         if seg_ind = seg2_ind then mk_true srk
                         else (mk_if srk (mk_lt srk sum sum2)
                                 (mk_leq srk (mk_one srk) trans_exec2.(trans_ind))))
                       exp_vars in
                   let global_req = mk_leq srk (mk_one srk) global_trans.(trans_ind) in
                   let res_assign = mk_eq srk res (mk_real srk (QQ.of_int trans_ind)) in
                   let sim2'_assignments =
                     let phs1_commuting = 
                       BatArray.fold_lefti
                         (fun termmap trans_comm_ind transformer ->
                            match E.exponentiate_rational transformer with
                            | None -> failwith "No decomp1"
                            | Some exp_m ->
                              let exp_term = 
                                if trans_comm_ind = trans_ind then
                                  mk_add srk [global_trans.(trans_comm_ind);
                                              mk_neg srk trans_exec.(trans_comm_ind);
                                              mk_neg srk (mk_one srk)]
                                else
                                  mk_add srk [global_trans.(trans_comm_ind);
                                              mk_neg srk trans_exec.(trans_comm_ind)]
                              in
                              expmatrix_to_term_array srk (fun i -> termmap.(i)) exp_m exp_term (QQMatrix.nb_rows this_seg.sim2))
                         (linmatrix_to_term_array srk 
                            (fun i -> match Linear.sym_of_dim i with 
                               | Some s' -> 
                                 begin match BatList.assoc_opt s' (BatList.map (fun (s, s') -> (s', s)) tr_symbols) with 
                                   | Some s -> mk_const srk s
                                   | None -> mk_const srk s'
                                 end
                               | None -> mk_real srk QQ.one) 
                            this_seg.sim1
                            (QQMatrix.nb_rows this_seg.sim1))
                         this_seg.phase1
                     in
                     let rhs =
                       BatArray.fold_lefti
                         (fun termmap trans_ac_ind (kind, transformer) ->
                            match kind with
                            | Ignore -> failwith "Ignore in exp"
                            | Reset -> termmap
                            | Commute ->
                              begin match E.exponentiate_rational transformer with
                                | None -> failwith "No decomp2"
                                | Some exp_m ->
                                  expmatrix_to_term_array srk (fun i -> termmap.(i)) exp_m trans_exec.(trans_ac_ind) 
                                    (QQMatrix.nb_rows this_seg.sim2)
                              end)
                         (linmatrix_to_term_array srk (fun i -> phs1_commuting.(i)) res_trans (QQMatrix.nb_rows this_seg.sim2))
                         this_seg.phase2 
                     in
                     Log.errorf "enter 1";
                     mk_eq_symmaps_LHS srk 
                       (linmatrix_to_term_array srk 
                          (fun i -> match Linear.sym_of_dim i with 
                             | Some s -> 
                               begin match BatList.assoc_opt s tr_symbols with 
                                 | Some s' -> mk_const srk s'
                                 | None -> mk_const srk s
                               end
                             | None -> mk_real srk QQ.one) 
                          this_seg.sim2
                          (QQMatrix.nb_rows this_seg.sim2))
                       rhs
                   in
                   mk_and srk (res_assign :: global_req :: sim2'_assignments :: more_recently_reset_phases_constr))
               this_seg.phase2
           in 
           let res_not_taken = 
             let res_assign = mk_eq srk res (mk_real srk (QQ.of_int (-1))) in
             let global_eq_seg =
               BatArray.to_list 
               @@
               BatArray.map2 (fun trans_seg trans_global -> mk_eq srk trans_seg trans_global)
                 trans_exec global_trans
             in
             let sim2'_assignments =
               let rhs =
                 BatArray.fold_lefti
                   (fun termmap trans_ac_ind (kind, transformer) ->
                      match kind with
                      | Ignore -> failwith "Ignore in exp"
                      | Reset -> termmap
                      | Commute ->
                        Log.errorf "Transformer is %a" (QQMatrix.pp) transformer;
                        begin match E.exponentiate_rational transformer with
                          | None -> Log.errorf "failed here %a" (QQMatrix.pp) transformer; failwith "No decomp3"
                          | Some exp_m ->
                            expmatrix_to_term_array srk (fun i -> termmap.(i)) exp_m trans_exec.(trans_ac_ind) (QQMatrix.nb_rows this_seg.sim2)
                        end)
                   (linmatrix_to_term_array srk 
                      (fun i -> match Linear.sym_of_dim i with 
                         | Some s' -> 
                           begin match BatList.assoc_opt s' (BatList.map (fun (s, s') -> (s', s)) tr_symbols) with 
                             | Some s -> mk_const srk s
                             | None -> mk_const srk s'
                           end
                         | None -> mk_real srk QQ.one) 
                      this_seg.sim2
                      (QQMatrix.nb_rows this_seg.sim2))
                   this_seg.phase2
               in
               Log.errorf "enter2";
               mk_eq_symmaps_LHS srk 
                 (linmatrix_to_term_array srk 
                    (fun i -> match Linear.sym_of_dim i with 
                       | Some s -> 
                         begin match BatList.assoc_opt s tr_symbols with 
                           | Some s' -> mk_const srk s'
                           | None -> mk_const srk s
                         end
                       | None -> mk_real srk QQ.one) 
                    this_seg.sim2
                    (QQMatrix.nb_rows this_seg.sim2))
                 rhs
             in
             mk_and srk (res_assign :: sim2'_assignments :: global_eq_seg)
           in
           mk_or srk [res_taken; res_not_taken])
          exp_vars)

  let commuting_seg_counter_eq_lc srk global_trans_exec lc =
    mk_eq srk (mk_add srk (BatArray.to_list global_trans_exec)) lc

  let phase_seg_counter_less_global_counters srk global_trans exp_vars =
    mk_and srk 
    @@ BatList.flatten
    @@ BatList.map
      (fun (trans_exec, _, _, _) ->
         BatArray.to_list
         @@ BatArray.map2 
           (fun trans_seg trans_global -> mk_leq srk trans_seg trans_global)
           trans_exec global_trans
      ) exp_vars





  let exp (srk : 'a context) tr_symbols loop_counter aclts =
    logf ~level:`always "%a" (pp srk tr_symbols) aclts;
    BatList.iter (fun (x, x') -> Log.errorf "sym x is %a x' is %a" (Syntax.pp_symbol srk) x (Syntax.pp_symbol srk) x) tr_symbols;
    if (List.length aclts = 0 || List.length aclts = 1 && QQMatrix.nb_rows (List.hd aclts).sim1 = 0) then  mk_true srk 
    else(
      let exp_vars = create_exp_vars srk aclts in
      let pairs = all_pairs exp_vars in
      let global_trans_exec = create_global_vars srk aclts in 
      let constr1 = (BatArray.to_list global_trans_exec) :: 
                    (BatList.map (fun (trans_exec, _, _, _) -> BatArray.to_list trans_exec) exp_vars)
                    |> List.flatten
                    |> mk_all_nonnegative srk in
      let constr2 = exp_reset_never_taken_constr srk exp_vars loop_counter in
      let constr3 = exp_perm_constraints srk pairs in
      let constr4 = exp_equality_reset_together_constraints srk pairs in
      let constr5 = commuting_seg_counter_eq_lc srk global_trans_exec loop_counter in
      let constr6 = phase_seg_counter_less_global_counters srk global_trans_exec exp_vars in
      let constr7 = exp_connect_sum_constraints srk exp_vars in
      let constr8 = stateless_last_reset_core_logic_constrs srk tr_symbols aclts exp_vars
          pairs global_trans_exec in
      mk_and srk [constr1; constr2; constr3; constr4; constr5; constr6; constr7; constr8]
    )

  let join srk tr_symbols aclts1 aclts2 = failwith "join"
  let widen srk tr_symbols aclts1 aclts2 = failwith "widen"
  let equal srk tr_symbols aclts1 aclts2 = failwith "eq"
end

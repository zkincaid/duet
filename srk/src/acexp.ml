open Syntax
open BatPervasives
module V = Linear.QQVector
module M = Linear.QQMatrix
module Z = Linear.ZZVector
module Q = Quantifier
module Int = SrkUtil.Int
module H = Abstract
module E = ExpPolynomial
open Linear

module VS = QQVectorSpace
include Log.Make(struct let name = "srk.aclts" end)

(* TODO: Experiment with affine hull of phi as scc transition function *)
(* sccvass is a vass abstraction such that
 * the control states (vertices) form a strongly connected
 * component.
 * graph[i][j] contains the set of vas transformers from
 * control state i to control state j (empty if no edge).
 * vas transformers must overapproximate transitions from 
 * transition states that model i to transition states that model 
 * j when s_lst is used as lin simulation.
 *
 * s_lst (simulation list) defined as in vas:
 *
 * Each matrix in S_lst starts at the 0th row. No S_lst
 * may contain the column representing all 0s.
 * The first row of the first item
 * in S_lst is matched with the first row of "a" and "b"
 * in a given transformer.
 *
 * There is exactly one item in S_lst for each coherence class
 * of V. A coherence class is defined as a set of rows that
 * reset together in every transformer.
 *
*)

type kind = Commute | Reset | Ignore

type phased_segment = {
  sim1 : QQMatrix.t;
  sim2 : QQMatrix.t;
  phase1 : QQMatrix.t array;
  phase2 : (kind * QQMatrix.t) array
}

type 'a t = phased_segment list


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
         if BatArray.exists (fun (kind, _) -> kind = Commute) ph_seg.phase2 then
           mk_const srk  (mk_symbol srk ~name:("R"^(string_of_int phase_ind)) `TyInt)
         else
           mk_real srk (QQ.of_int (-1))
       in
       let ph2_entrance_vals =
         BatList.map (fun row -> 
             mk_const srk (mk_symbol srk ~name:(Format.sprintf "S%d,%d" phase_ind row) `TyReal))
           (BatList.of_enum (0 -- (M.nb_rows ph_seg.sim2)))
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


let linmatrix_to_term_array srk term_vec matrix =
   QQMatrix.rowsi matrix
   /@ (fun (_, row) -> Linear.term_of_vec srk term_vec row)
   |> BatArray.of_enum

let expmatrix_to_term_array srk term_vec matrix exp_term =
   E.Matrix.rowsi matrix
   /@ (fun (_, row) -> E.term_of_vec srk term_vec exp_term row)
   |> BatArray.of_enum


let mk_eq_symmaps_LHS srk a1 a2 =
  mk_and srk 
  @@ BatArray.to_list 
  @@ BatArray.mapi
    (fun ind term ->
       mk_eq srk term a2.(ind))
    a1

let simmatrix_to_termarray srk simmat =
  let entryfun = (fun entry -> mk_real srk entry) in
 let outputarr = (BatArray.make (M.nb_rows simmat) (mk_zero srk)) in
  BatEnum.iter
    (fun (dim1, dim2, entry) ->
       if dim1 = -1 then ()
       else (
         let symterm = 
           if dim2 = -1 then failwith "Const dim in lin comb for non-const dim row"
           else mk_const srk (symbol_of_int dim2)
         in
         outputarr.(dim1)<-
           mk_add srk [mk_mul srk [entryfun entry; symterm]; outputarr.(dim1)])) 
    (M.entries simmat);
  outputarr





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
                                 | None -> failwith "No decomp"
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
                                   expmatrix_to_term_array srk (fun i -> termmap.(i)) exp_m exp_term)
                              (linmatrix_to_term_array srk 
                                 (fun i -> match Linear.sym_of_dim i with 
                                    | Some s' -> 
                                      begin match BatList.assoc_opt s' (BatList.map (fun (s, s') -> (s', s)) tr_symbols) with 
                                        | Some s -> mk_const srk s
                                        | None -> mk_const srk s'
                                      end
                                    | None -> mk_real srk QQ.one) 
                                 this_seg.sim1)
                              this_seg.phase1
                          in
                          let rhs =
                           BatArray.fold_lefti
                            (fun termmap trans_ac_ind (kind, transformer) ->
                              match E.exponentiate_rational transformer with
                              |None -> failwith "No decomp"
                              | Some exp_m ->
                                expmatrix_to_term_array srk (fun i -> termmap.(i)) exp_m trans_exec.(trans_ac_ind))
                            (linmatrix_to_term_array srk (fun i -> phs1_commuting.(i)) res_trans)
                            this_seg.phase2
                          in
                          mk_eq_symmaps_LHS srk 
                            (linmatrix_to_term_array srk 
                               (fun i -> match Linear.sym_of_dim i with 
                                  | Some s -> 
                                    begin match BatList.assoc_opt s tr_symbols with 
                                      | Some s' -> mk_const srk s'
                                      | None -> mk_const srk s
                                    end
                                  | None -> mk_real srk QQ.one) 
                               this_seg.sim2)
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
                    match E.exponentiate_rational transformer with
                    |None -> failwith "No decomp"
                    | Some exp_m ->
                      expmatrix_to_term_array srk (fun i -> termmap.(i)) exp_m trans_exec.(trans_ac_ind))
                 (linmatrix_to_term_array srk 
                    (fun i -> match Linear.sym_of_dim i with 
                       | Some s' -> 
                         begin match BatList.assoc_opt s' (BatList.map (fun (s, s') -> (s', s)) tr_symbols) with 
                           | Some s -> mk_const srk s
                           | None -> mk_const srk s'
                         end
                       | None -> mk_real srk QQ.one) 
                    this_seg.sim2)
                 this_seg.phase2
             in
             mk_eq_symmaps_LHS srk 
               (linmatrix_to_term_array srk 
                  (fun i -> match Linear.sym_of_dim i with 
                     | Some s -> 
                       begin match BatList.assoc_opt s tr_symbols with 
                         | Some s' -> mk_const srk s'
                         | None -> mk_const srk s
                       end
                     | None -> mk_real srk QQ.one) 
                  this_seg.sim2)
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

(*TODO:Make a better pp function*)
let pp srk tr_symbols formatter aclts = 
  Format.fprintf formatter "Printing aclts";
  BatList.iteri (fun ind seg ->
      Format.fprintf formatter "Currently Printing Phase %n \n _________________________ \n" ind;
      Format.fprintf formatter "Sim1 matrix is %a \n" (QQMatrix.pp) seg.sim1;
      Format.fprintf formatter "\n\nPrinting sim1 Arrays: \n";
      BatArray.iteri (fun indmat mat ->
          Format.fprintf formatter "Phase 1 transformer %d is \n %a \n\n" indmat (QQMatrix.pp) mat) seg.phase1;
      Format.fprintf formatter "Sim2 matrix is %a \n" (QQMatrix.pp) seg.sim1;
      Format.fprintf formatter "\n\nPrinting sim2 Arrays: \n";
      BatArray.iteri (fun indmat (kind, mat) ->
          match kind with
          | Reset ->
            Format.fprintf formatter "Phase 2 transformer %d is RESET and is \n %a \n\n" indmat (QQMatrix.pp) mat
          | Commute ->
            Format.fprintf formatter "Phase 2 transformer %d is COMMUTE and is \n %a \n\n" indmat (QQMatrix.pp) mat
          | Ignore ->
            Format.fprintf formatter "Phase 2 transformer %d is IGNORE and is \n %a \n\n" indmat (QQMatrix.pp) mat
        ) seg.phase2) 
    aclts





let exp (srk : 'a context) tr_symbols loop_counter aclts =
  logf ~level:`always "%a" (pp srk tr_symbols) aclts;
  if (List.length aclts = 0) then failwith "Case of no phase segments not yet handled... prob just do mk_true here" 
  else(
    Log.errorf "1";
    let exp_vars = create_exp_vars srk aclts in
    let pairs = all_pairs exp_vars in
    let global_trans_exec = create_global_vars srk aclts in 
    Log.errorf "2";
    let constr1 = (BatArray.to_list global_trans_exec) :: 
      (BatList.map (fun (trans_exec, _, _, _) -> BatArray.to_list trans_exec) exp_vars)
    |> List.flatten
                |> mk_all_nonnegative srk in
    let constr2 = exp_reset_never_taken_constr srk exp_vars loop_counter in
    let constr3 = exp_perm_constraints srk pairs in
    Log.errorf "3";
    let constr4 = exp_equality_reset_together_constraints srk pairs in
    let constr5 = commuting_seg_counter_eq_lc srk global_trans_exec loop_counter in
    let constr6 = phase_seg_counter_less_global_counters srk global_trans_exec exp_vars in
    let constr7 = exp_connect_sum_constraints srk exp_vars in
    Log.errorf "4";
    let constr8 = stateless_last_reset_core_logic_constrs srk tr_symbols aclts exp_vars
        pairs global_trans_exec in
    Log.errorf "5";
    mk_and srk [constr1; constr2; constr3; constr4; constr5; constr6; constr7; constr8]
  )

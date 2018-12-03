open Syntax
open BatPervasives
module LRI = Iteration.LinearRecurrenceInequation
module PG = Iteration.PolyhedronGuard
module V = Linear.QQVector
module M = Linear.QQMatrix
module Z = Linear.ZZVector
module Monomial = Polynomial.Monomial
module P = Polynomial.QQXs
module Scalar = Apron.Scalar
module Coeff = Apron.Coeff
module Abstract0 = Apron.Abstract0
module Linexpr0 = Apron.Linexpr0
module Lincons0 = Apron.Lincons0
module Dim = Apron.Dim
module Q = Quantifier

module CS = CoordinateSystem
module A = BatDynArray

module IntSet = SrkUtil.Int.Set
module H = Abstract
include Log.Make(struct let name = "srk.vass" end)
open Mdvas
module Mvass = Mdvas.Mdvass
module Int = SrkUtil.Int




module Vassnew = struct

  type 'a sccvas = 
    { label : ('a formula) array;
      graph : vas array array;
      simulation : M.t list;
      invars : 'a formula list;
      invarmaxk : bool
    }

  type 'a t = {
    vasses : 'a sccvas array;
    formula : 'a formula
  }

  module BoolGraph = struct
    type t = bool array array

    module V = Int
    let is_directed = true
    let iter_vertex f g =
      BatEnum.iter f (0 -- (Array.length g - 1))
    let iter_succ f g v = Array.iteri (fun ind ele -> if ele then f ind ) g.(v)
    let fold_vertex f g a = BatEnum.fold (fun acc v -> f v acc) a (0 -- (Array.length g - 1))
    let fold_succ f g v a = BatArray.fold_righti (fun ind ele acc -> if ele then f ind acc else acc) g.(v) a
  end

  module BGraphComp = Graph.Components.Make(BoolGraph)
  module BGraphTrav = Graph.Traverse.Dfs(BoolGraph)
  module BGraphTopo = Graph.Topological.Make(BoolGraph)
  module VassGraph = struct
    type t = vas array array

    module V = Int
    let is_directed = true
    let iter_vertex f g =
      BatEnum.iter f (0 -- (Array.length g - 1))
    let iter_succ f g v = Array.iteri (fun ind ele -> if not (TSet.is_empty ele) then f ind ) g.(v)
    let fold_vertex f g a = BatEnum.fold (fun acc v -> f v acc) a (0 -- (Array.length g - 1))
    let fold_succ f g v a = BatArray.fold_righti (fun ind ele acc -> if not (TSet.is_empty ele) then f ind acc else acc) g.(v) a
  end

  module GraphComp = Graph.Components.Make(VassGraph) 
  module GraphTrav = Graph.Traverse.Dfs(VassGraph)
  module Accelerate =
    Iteration.MakeDomain(Iteration.Product(Iteration.LinearRecurrenceInequation)(Iteration.PolyhedronGuard))





  (*Determine if there is transition from l1 to l2*)
  let is_connected_two_nodes srk l1 l2 tr_symbols formula =
    let solver = Smt.mk_solver srk in
    Smt.Solver.reset solver;
    let form = (rewrite srk ~down:(nnf_rewriter srk) (mk_and srk [l1; postify srk tr_symbols l2; formula])) in
    Smt.Solver.add solver [form];
    match Smt.Solver.get_model solver with
    | `Unsat -> false
    | `Unknown -> true
    | `Sat _ -> true



  (*Given set of labels and formula, compute graph*)
  let compute_edges srk tr_symbols label formula =
    let graph = Array.make_matrix (Array.length label) (Array.length label) false in
    BatArray.iteri (fun ind1 arr ->
        BatArray.modifyi (fun ind2 _ ->
            is_connected_two_nodes srk label.(ind1) label.(ind2)  tr_symbols formula)
          arr)
      graph;
    graph


  let compute_single_scc_vass ?(exists=fun x -> true) srk tr_symbols labels_lst orig_form =
    let formula = mk_and srk [mk_or srk labels_lst; orig_form] in(*Don't really need orig_form here*)
    let {v; alphas;invars;invarmaxk} = abstract ~exists srk tr_symbols formula in
    (*This will be replaced in next iteration with localized transformers*)
    let graph = Mvass.compute_edges srk v tr_symbols alphas (Array.of_list labels_lst) formula in
    {label=Array.of_list labels_lst;graph;simulation=alphas;invars;invarmaxk}


  let pp srk syms formatter vasses = 
    BatArray.iteri (fun ind sccvas ->
        Format.fprintf formatter "Vass %n has the following labels \n" ind;
        BatArray.iteri (fun ind2 lab -> Format.fprintf formatter "Label %n is %a \n" ind2 (Formula.pp srk) (lab)) sccvas.label;
        Format.fprintf formatter "END LABELS \n\n" ;
        Format.fprintf formatter "Vass %n has the following graph \n" ind;
        BatArray.iteri (fun ind arr ->
            BatArray.iteri (fun ind2 trans ->
                Format.fprintf formatter "Num connections from label %d to label %d is: %d \n" ind ind2 (TSet.cardinal trans);
                TSet.iter (fun trans ->
                    Format.fprintf formatter "Label %d admits trans a: %a b: %a \n" ind (Z.pp) trans.a (V.pp) trans.b) trans) arr) sccvas.graph;
        Format.fprintf formatter "END PRINT GRAPH \n\n";
        Format.fprintf formatter "Vass %n has the following alphas \n" ind;
        BatList.iter (fun alph -> Format.fprintf formatter "Matrix %a\n" (M.pp) alph) sccvas.simulation) vasses.vasses




  let pre_symbols tr_symbols =
    List.fold_left (fun set (s,_) ->
        Symbol.Set.add s set)
      Symbol.Set.empty
      tr_symbols

  let post_symbols tr_symbols =
    List.fold_left (fun set (_,s') ->
        Symbol.Set.add s' set)
      Symbol.Set.empty
      tr_symbols


  let get_pre_cube_labels srk formula exists tr_symbols =
    let pre_symbols = pre_symbols tr_symbols in
    let post_symbols = post_symbols tr_symbols in
    let solver = Smt.mk_solver srk in
    let exists_pre x =
      exists x && not (Symbol.Set.mem x post_symbols)
    in
    let exists_post x =
      exists x && not (Symbol.Set.mem x pre_symbols)
    in
    let rec find_pre labels =
      match Smt.Solver.get_model solver with
      | `Unsat -> labels
      | `Unknown -> assert false
      | `Sat m ->
        match Interpretation.select_implicant m formula with
        | None -> assert false
        | Some imp ->
          Log.errorf "entry";
          let pre_imp = Q.local_project_cube srk exists_pre m imp in
          Smt.Solver.add solver [mk_not srk (mk_and srk pre_imp)];
          Log.errorf "exit";
          Log.errorf "Num: %d" (List.length labels);
          find_pre ((mk_and srk pre_imp) :: labels)
    in
    Smt.Solver.reset solver;
    Smt.Solver.add solver [SrkSimplify.simplify_terms srk formula];
    let pre_labels = find_pre [] in
    let post_form = (rewrite srk ~down:(nnf_rewriter srk) 
                       (mk_and srk [formula; mk_not srk (postify srk tr_symbols (mk_or srk pre_labels))])) in

    let rec find_post labels =
      Log.errorf "yEEE";
      match Smt.Solver.get_model solver with
      | `Unsat -> labels
      | `Unknown -> assert false
      | `Sat m ->
        match Interpretation.select_implicant m post_form with
        | None -> assert false
        | Some imp ->
          let post_imp = Q.local_project_cube srk exists_post m imp in
          Smt.Solver.add solver [mk_not srk (mk_and srk post_imp)];
          Log.errorf "exit";
          Log.errorf "Post lab Num: %d" (List.length labels);
          find_post ((preify srk tr_symbols (mk_and srk post_imp)) :: labels)
    in
    Smt.Solver.reset solver;
    Smt.Solver.add solver [post_form];
    let post_labels = find_post [] in
    pre_labels, post_labels


  (*Given a set of labels, combine labels that overlap...likely much more efficient way to do this*)
  let get_largest_polyhedrons srk labels =
    let rec helper_sing front ele back changed =
      match back with
      | [] -> front, ele, changed
      | hd :: tl ->
        let solver = Smt.mk_solver srk in
        let form = (rewrite srk ~down:(nnf_rewriter srk) (mk_and srk [ele; hd])) in 
        Smt.Solver.add solver [form];
        match Smt.Solver.get_model solver with
        | `Unsat -> helper_sing (hd :: front) ele tl changed
        | `Unknown -> helper_sing (hd :: front) ele tl changed
        | `Sat m -> helper_sing front (mk_or srk [ele; hd]) tl true
    in

    let rec loop_labels front back =
      match back with
      | [] -> front
      | hd :: tl ->
        let b', el, ch = helper_sing [] hd tl false in
        if ch = true 
        then loop_labels front (el :: b')
        else loop_labels (el :: front) b'
    in
    loop_labels [] labels

  let get_intersect_cube_labeling srk formula exists tr_symbols =
    let pre, post = get_pre_cube_labels srk formula exists tr_symbols in
    let pre', post' = get_largest_polyhedrons srk pre, get_largest_polyhedrons srk post in
    let result = BatArray.of_list (post' @ pre') in
    result


  let abstract ?(exists=fun x -> true) srk tr_symbols body =
    let body = (rewrite srk ~down:(nnf_rewriter srk) body) in
    let body = Nonlinear.linearize srk body in
    let label = get_intersect_cube_labeling srk body exists tr_symbols in
    let graph = compute_edges srk tr_symbols label body in
    let num_sccs, func_sccs = BGraphComp.scc graph in
    let sccs = Array.make num_sccs  [] in
    BatArray.iteri (fun ind lab -> sccs.(func_sccs ind)<-(lab :: sccs.(func_sccs ind)))
      label;
    if num_sccs = 0 then
      {vasses= BatArray.init 0 (fun x -> assert false); formula=body}
    else(
      let vassarrays = BatArray.map (fun scc -> compute_single_scc_vass ~exists srk tr_symbols scc body) sccs in
      let result = {vasses=vassarrays;formula=body} in
      logf ~level:`always "%a" (pp srk tr_symbols) result;
      result
    )


  (*Create array of list of indices of transformers going in and out of a single label*)
  let exp_compute_trans_in_out_index_numbers transformersmap num =
    let in_sing, out_sing = Array.make num [], Array.make num [] in
    List.iteri (fun index (n1, trans, n2) -> in_sing.(n2)<-(index :: in_sing.(n2)); out_sing.(n1)<- (index :: out_sing.(n1)))
      transformersmap;
    in_sing, out_sing


  (*each entry and exit label has value 1 or 0*)
  let exp_each_ests_one_or_zero srk ests =
    (*This optimization seems to greatly reduce runtime for more complex cases*)
    if (List.length ests = 1) then
      (
        let (es, et) = List.hd ests in
        mk_and srk [mk_eq srk es (mk_one srk); mk_eq srk et (mk_one srk)]
      )
    else(
      mk_and srk
        (List.map (fun (es, et) -> 
             mk_and srk
               [mk_or srk [mk_eq srk es (mk_zero srk); mk_eq srk es (mk_one srk)];
                mk_or srk [mk_eq srk et (mk_zero srk); mk_eq srk et (mk_one srk)]]
           )
            ests))

  (*An entry and an exit label must be taken. Note this is stronger than prev vass in which label must be taken or
   * loop counter is 0*)
  let exp_one_in_out_flow srk ests = 
    let et, es = List.split ests in
      mk_and srk 
        [mk_eq srk (mk_add srk et) (mk_one srk);
         mk_eq srk (mk_add srk es) (mk_one srk)]




(* Flow is conserved for labels. Used both for master flow and also for equiv class flow *)
let exp_consv_of_flow_new srk in_sing out_sing ests varst reset_trans =
  let in_sing_inds = in_sing in
  let in_sing = BatArray.map (fun indlist -> List.map (fun ind -> List.nth varst ind) indlist) in_sing in
  let out_sing = BatArray.map (fun indlist -> List.map (fun ind -> List.nth varst ind) indlist) out_sing in
  mk_and srk
    (List.mapi (fun ind (es, et) ->
         mk_eq srk
           (mk_add srk ((if reset_trans = -2 then es else if (BatList.mem reset_trans in_sing_inds.(ind)) 
                         then mk_one srk else mk_zero srk) :: in_sing.(ind)))
           (mk_add srk (et :: out_sing.(ind))))
        ests)


  (*Either svar for each row in equiv class in x and equiv class not reset or equiv class reset
   * at transformer i and svars equal the reset dim at transformer i*)
  let exp_sx_constraints_helper_flow srk ri ksum ksums svarstdims transformers kvarst unialpha tr_symbols kstack in_sing
      out_sing ests =
    mk_or srk
      ((mk_and srk
          (mk_eq srk ri (mk_real srk (QQ.of_int (-1))) ::
           (List.map
              (fun (svart, dim) -> 
                 mk_eq srk svart (preify srk tr_symbols (Linear.of_linterm srk (M.row dim unialpha))))
              svarstdims)))
       :: (BatList.mapi 
             (fun ind {a; b} -> 
                if ZZ.equal (Z.coeff (snd (List.hd svarstdims)) a) ZZ.one then (mk_false srk)
                          else (
                            mk_and srk
                              (exp_consv_of_flow_new srk in_sing out_sing ests kstack ind ::
                               (mk_eq srk ri (mk_real srk (QQ.of_int ind))) ::
                               exp_other_reset srk ksum ksums kvarst ind ::
                               (List.map
                                  (fun (svart, dim) -> mk_eq srk svart (mk_real srk (V.coeff dim b))) svarstdims)))
                        ) 
             transformers))


  (*See helper function for description*)
  let exp_sx_constraints_flow srk equiv_pairs transformers kvarst ksums unialpha tr_symbols in_sing out_sing ests =
    mk_and srk
      (List.map (fun (kstack, svarstdims, ri, ksum) ->
           exp_sx_constraints_helper_flow srk ri ksum ksums svarstdims transformers kvarst unialpha tr_symbols kstack in_sing out_sing ests)
          equiv_pairs)


  (*The N vars are the max number of times any transition was taken. Used for flow primarily*)
  let rec create_n_vars srk num vars basename =
    begin match num <= 0 with
      | true -> List.rev vars (*rev only to make debugging easier and have names match up... not needed *)
      | false -> create_n_vars srk (num - 1) ((mk_symbol srk ~name:(basename^(string_of_int num)) `TyInt) :: vars) basename
    end



  (*ESL entry node for graph; ETL exit node for graph*)
  let create_es_et srk num =
    let es = map_terms srk (create_n_vars srk num [] "ESL") in
    let et = map_terms srk (create_n_vars srk num [] "ETL") in
    List.combine es et

 (* The initial label for graph must have precond satisfied; the final label for graph must have 
   * post cond satisfied*)
  let exp_pre_post_conds srk ests label tr_symbols =
    mk_and srk
      (List.mapi (fun ind (es, et) ->
           mk_and srk
             [mk_if srk (mk_eq srk es (mk_one srk)) (label.(ind));
              mk_if srk (mk_eq srk et (mk_one srk)) (postify srk tr_symbols (label.(ind)))])
          ests)

  (*Set N vars eq to loop counter*)
  let exp_nvars_eq_loop_counter srk nvarst loop_counter =
    mk_eq srk (mk_add srk nvarst) loop_counter


  (* Set each kvar less or eq respective nvar*)
  let exp_kvarst_less_nvarst srk nvarst kvarst =
    mk_and srk
      (List.map (fun kstack ->
           mk_and srk
             (List.mapi (fun ind k ->
                  mk_leq srk k (List.nth nvarst ind))
                 kstack))
          kvarst)


  (*Compute the graph that is reachable from a given transformer*)
  let get_reachable_trans graph =
    BatArray.mapi (fun ind vert -> GraphTrav.fold_component (fun v (trans, verts) -> 
        TSet.union
          (List.fold_left 
             (fun acc ele ->
                TSet.union acc 
                  (TSet.union graph.(ele).(v) graph.(v).(ele))) trans verts)
          graph.(v).(v),
        v :: verts)
        (TSet.empty, []) graph ind) graph


  (*MAKE LOOP_COUNTER AT LEAST 1.... but does this enforce other things must transition?....YOU NEED TO IMPLEMENT THE RESET SHIT*)
  let closure_of_an_scc srk tr_symbols loop_counter vass =
    let label, graph, alphas, invars, invarmaxk = vass.label, vass.graph, vass.simulation, vass.invars, vass.invarmaxk in
    let simulation = alphas in

    let ests = create_es_et srk (Array.length label) in
    let in_out_one = exp_one_in_out_flow srk ests in
    let ests_one_or_zero = exp_each_ests_one_or_zero srk ests in
    let pre_post_conds = exp_pre_post_conds srk ests label tr_symbols in
    let pos_constraints_1 = create_exp_positive_reqs srk [fst (List.split ests); snd (List.split ests)] in

    if(M.nb_rows (unify (vass.simulation)) = 0) then
      ((mk_and srk [in_out_one; ests_one_or_zero; pre_post_conds; pos_constraints_1]), (fst (List.split ests)))
    else(
      let transformersmap : (int * transformer * int) list = List.flatten
          (List.flatten
             (Array.to_list
                (Array.mapi (fun n1 arr ->
                     Array.to_list (Array.mapi (fun n2 vas ->
                         BatEnum.fold (fun acc trans -> (n1, trans, n2) :: acc) [] (TSet.enum vas))
                         arr))
                    graph)))
      in
      let transformers = List.map (fun (_, t, _) -> t) transformersmap in
      let nvarst = map_terms srk (create_n_vars srk (List.length transformers) [] "N") in
      let (form, (equiv_pairst, kvarst, ksumst)) =
        exp_base_helper srk tr_symbols loop_counter simulation transformers invars invarmaxk in
      let sum_n_eq_loop_counter = exp_nvars_eq_loop_counter srk nvarst loop_counter in
      let ks_less_than_ns = exp_kvarst_less_nvarst srk nvarst kvarst in
      let reachable_transitions = get_reachable_trans graph in
      let post_conds_const = Mvass.exp_post_conds_on_transformers srk label transformersmap reachable_transitions nvarst alphas tr_symbols loop_counter in

      let in_sing, out_sing  = exp_compute_trans_in_out_index_numbers transformersmap (Array.length label) in
      let flow_consv_req = exp_consv_of_flow_new srk in_sing out_sing ests nvarst (-2) in
      let pos_constraints = create_exp_positive_reqs srk [nvarst] in
      let sx_constraints = exp_sx_constraints_flow srk equiv_pairst transformers (nvarst:: kvarst) 
          ((mk_add srk nvarst) :: ksumst) (unify alphas) tr_symbols in_sing out_sing
          ests in
      let form = mk_and srk [form; sum_n_eq_loop_counter; ks_less_than_ns; flow_consv_req; in_out_one;
                             ests_one_or_zero; pre_post_conds; pos_constraints; pos_constraints_1; post_conds_const; sx_constraints] in
      form, (fst (List.split ests)))



  let rec valid_ordering ordering sccgraph =
    match ordering with
    | [] -> assert false
    | [hd] -> true
    | hd :: hdd :: tl ->
      if sccgraph.(hd).(hdd) then valid_ordering (hdd :: tl) sccgraph
      else false


  let merge_mappings pre post use_pres_post use_posts_pre =
    BatList.fold_left2 (fun acc (x, x') (y, y') -> 
        if use_posts_pre then (
          if use_pres_post then (x',  y) :: acc
          else (x, y) :: acc
        )
        else if use_pres_post then (x', y') :: acc
        else (x, y') :: acc) [] pre post

  let no_trans_taken srk loop_counter syms =
    let eqs = (List.map (fun (x, x') -> mk_eq srk (mk_const srk x) (mk_const srk x'))) syms in
    mk_and srk ((mk_eq srk loop_counter (mk_zero srk)) :: eqs)


  let ordering_bounds srk ordering_vars max =
    mk_and srk (BatArray.to_list (BatArray.map (fun var -> mk_and srk 
                                                  [mk_leq srk (mk_zero srk) var;
                                                   mk_lt srk var max]) ordering_vars))


  let no_dups_ordering srk ordering_vars =
    let ord_list = BatArray.to_list ordering_vars in
    let rec helper_no_dups ele ord_tl =
      match ord_tl with
      | [] -> []
      | hd :: tl -> mk_not srk (mk_eq srk ele hd) :: (helper_no_dups ele tl)
    in
    let rec helper_no_dups_2 ord_tl =
      match ord_tl with
      | [] -> []
      | hd :: tl -> (helper_no_dups_2 tl) @ (helper_no_dups hd tl)
    in
    mk_and srk (helper_no_dups_2 ord_list)


  let come_next_req srk ordering_vars es loop_counters num_scc_used scc_closures symmappings syms formula =
    mk_and srk (BatList.flatten (BatArray.to_list (BatArray.mapi (fun ind1 o_var1 ->
        BatArray.to_list (BatArray.mapi (fun ind2 o_var2 ->
            if ind1 <> ind2 then(
              mk_if srk (mk_eq srk o_var1 (mk_sub srk o_var2 (mk_one srk)))
                (mk_ite srk (mk_eq srk (mk_add srk es.(ind1)) (mk_zero srk))
                   (mk_and srk [(mk_eq srk (mk_add srk es.(ind2)) (mk_zero srk));
                                mk_eq srk loop_counters.(ind2) (mk_zero srk)])
                   (mk_or srk [(mk_and srk [(mk_eq srk (mk_add srk es.(ind2)) (mk_zero srk));
                                            mk_eq srk loop_counters.(ind2) (mk_zero srk);
                                            mk_eq srk num_scc_used o_var1]);
                               mk_and srk [scc_closures.(ind2);
                                           (postify srk (merge_mappings syms symmappings.(ind2) true true) 
                                              (postify srk (merge_mappings syms symmappings.(ind1) false false) formula));
                                           mk_leq srk o_var2 num_scc_used]])))
            else (mk_true srk))
            ordering_vars)) ordering_vars)))


  let first_scc_used srk ordering_vars es sccs_closures symmappings syms =
    mk_and srk (BatArray.to_list (BatArray.mapi (fun ind1 o_var1 ->
        mk_if srk (mk_eq srk o_var1 (mk_zero srk))
          (mk_and srk (mk_eq srk (mk_add srk es.(ind1)) (mk_one srk) :: sccs_closures.(ind1) ::
                       (BatList.map2 (fun (x, x') (sccx, sccx') -> mk_eq srk (mk_const srk x) (mk_const srk sccx))
                          syms symmappings.(ind1))))) ordering_vars))

  let used_last_scc srk orderings_vars num_scc_used symmappings syms =
    mk_and srk (BatArray.to_list (BatArray.mapi (fun ind1 o_var1 ->
        mk_if srk (mk_eq srk o_var1 num_scc_used)
          (mk_and srk (BatList.map2 (fun (x, x') (sccx, sccx') -> mk_eq srk (mk_const srk x') (mk_const srk sccx'))
                         syms symmappings.(ind1)))) orderings_vars))

  let topo_order_constraints srk order es scc_ordering =
    let rec helper ind1 remaining_order =
      match remaining_order with
      | [] -> []
      | hd :: tl -> mk_if srk (mk_lt srk scc_ordering.(hd) scc_ordering.(ind1)) (mk_eq srk (mk_zero srk) (mk_add srk es.(ind1))) :: (helper ind1 tl)
    in
    let rec outer ordering =
      match ordering with
      | [] -> []
      | hd :: tl -> (helper hd tl) :: (outer tl)
    in
    mk_and srk (List.flatten (outer order))

  let exp srk syms loop_counter sccsform =
    if BatArray.length sccsform.vasses = 0 then (mk_false srk) else(
      let subloop_counters = BatArray.mapi (fun ind1 scc ->
          mk_const srk ((mk_symbol srk ~name:("counter_"^(string_of_int ind1)) `TyInt))) sccsform.vasses in
      let symmappings = BatArray.mapi (fun ind1 scc ->
          List.rev
            (BatList.fold_lefti (fun acc ind2 (x, x') ->
                 ((mk_symbol srk ~name:("x_"^(string_of_int ind1)^"COM"^(string_of_int ind2)) (typ_symbol srk x)),
                  (mk_symbol srk ~name:("x'_"^(string_of_int ind1)^"COM"^(string_of_int ind2)) (typ_symbol srk x'))) :: acc) [] syms)) sccsform.vasses
      in
      let sccclosures_es = BatArray.mapi (fun ind vass -> closure_of_an_scc srk syms subloop_counters.(ind) vass) sccsform.vasses in
      let sccclosures, es = BatList.split (BatArray.to_list sccclosures_es) in
      let sccclosures, es = BatArray.of_list sccclosures, BatArray.of_list es in
      let sccclosures = BatArray.mapi (fun ind closure ->  
          (postify srk (merge_mappings syms symmappings.(ind) false true) 
             (postify srk (merge_mappings syms symmappings.(ind) true false) closure))) sccclosures in

      let scclabels = BatArray.map (fun scc -> mk_or srk (BatArray.to_list scc.label)) sccsform.vasses in		
      let sccgraph = compute_edges srk syms scclabels sccsform.formula in


      let num_scc_used = mk_const srk (mk_symbol srk ~name:("Num_scc_used") `TyInt) in
      let order = List.rev (BGraphTopo.fold (fun v acc -> Log.errorf "THIS SCC REACHED %d" v; v :: acc) sccgraph []) in


      let sub_loops_geq_0 = create_exp_positive_reqs srk [Array.to_list subloop_counters] in
      let scc_ordering = BatArray.mapi (fun ind1 scc ->
          mk_const srk ((mk_symbol srk ~name:("ordering_"^(string_of_int ind1)) `TyInt))) sccsform.vasses in


      let order_bounds_const = ordering_bounds srk scc_ordering (mk_real srk (QQ.of_int (BatArray.length sccclosures))) in
      let no_dups_constr = no_dups_ordering srk scc_ordering in
      let come_next_const = come_next_req srk scc_ordering es subloop_counters num_scc_used sccclosures symmappings syms sccsform.formula in
      let first_scc_const = first_scc_used srk scc_ordering es sccclosures symmappings syms in
      let last_scc_const = used_last_scc srk scc_ordering num_scc_used symmappings syms in
      let num_scc_used_bound = mk_lt srk num_scc_used (mk_real srk (QQ.of_int (BatArray.length sccclosures))) in
      let loop_bound = mk_eq srk (mk_add srk (num_scc_used :: (BatArray.to_list subloop_counters))) loop_counter in

      let order_constr = topo_order_constraints srk order es scc_ordering in
      let debug = mk_eq srk scc_ordering.(0) (mk_zero srk) in 
      let result = mk_or srk [mk_and srk [order_bounds_const; sub_loops_geq_0; no_dups_constr; come_next_const; first_scc_const;
                                          last_scc_const; num_scc_used_bound; loop_bound; mk_leq srk (mk_zero srk) loop_counter; order_constr];
                              no_trans_taken srk loop_counter syms] in
      (*let result = mk_and srk [sccclosures.(1); sub_loops_geq_0; mk_eq srk subloop_counters.(1) loop_counter] in*)
      Log.errorf "Done";
      result
    )



  let join _ _ _ _ = assert false
  let widen _ _ _ _ = assert false
  let equal _ _ _ _ = assert false


end

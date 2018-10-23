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



  let is_connected_two_nodes srk l1 l2 tr_symbols formula =
    let solver = Smt.mk_solver srk in
    Smt.Solver.reset solver;
    let form = (rewrite srk ~down:(nnf_rewriter srk) (mk_and srk [l1; postify srk tr_symbols l2; formula])) in
    Smt.Solver.add solver [form];
    match Smt.Solver.get_model solver with
    | `Unsat -> false
    | `Unknown -> true
    | `Sat _ -> true



  let compute_edges srk tr_symbols label formula =
    let graph = Array.make_matrix (Array.length label) (Array.length label) false in
    BatArray.iteri (fun ind1 arr ->
        BatArray.modifyi (fun ind2 _ ->
            is_connected_two_nodes srk label.(ind1) label.(ind2)  tr_symbols formula)
          arr)
      graph;
    graph


  let compute_single_scc_vass ?(exists=fun x -> true) srk tr_symbols labels_lst orig_form =
    let formula = mk_and srk [mk_or srk labels_lst; orig_form] in
    Log.errorf "formula for this vass: %a" (Formula.pp srk) formula;
    let {v; alphas;invars;invarmaxk} = abstract ~exists srk tr_symbols formula in
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


  let abstract ?(exists=fun x -> true) srk tr_symbols body =
    Log.errorf "Init formula %a" (Formula.pp srk) body;
    let body = (rewrite srk ~down:(nnf_rewriter srk) body) in
    let body = Nonlinear.linearize srk body in
    Log.errorf "Post rewrite formula %a" (Formula.pp srk) body;
    let label = Mvass.get_intersect_cube_labeling srk body exists tr_symbols in

    let graph = compute_edges srk tr_symbols label body in
    let num_sccs, func_sccs = BGraphComp.scc graph in
    let sccs = Array.make num_sccs  [] in
    BatArray.iteri (fun ind lab -> sccs.(func_sccs ind)<-(lab :: sccs.(func_sccs ind)))
      label;
    if num_sccs = 0 then (
      (*{vasses= BatArray.make 1 {label=BatArray.make 1 (mk_false srk);
                                graph=BatArray.make 1 (BatArray.make 1 (TSet.empty));
                                simulation = [ident_matrix srk tr_symbols];
                                invars = [];
                                invarmaxk = false};
          formula = body})*) assert false;)
    else(

    let vassarrays = BatArray.map (fun scc -> compute_single_scc_vass ~exists srk tr_symbols scc body) sccs in
    let result = {vasses=vassarrays;formula=body} in
    Log.errorf "LOOK HERE";
    let b = Buffer.create 16 in
    logf ~level:`always "%a" (pp srk tr_symbols) result;
    result)



  let rec sublists = function (*I stole this from the internet. Hopefully it works*)
    | []    -> [[]]
    | x::xs -> let ls = sublists xs in
      List.map (fun l -> x::l) ls @ ls


  let exp_compute_trans_in_out_index_numbers transformersmap num  nvarst =
    let in_sing, out_sing = Array.make num [], Array.make num [] in
    List.iteri (fun index (n1, trans, n2) -> in_sing.(n2)<-((List.nth nvarst index) :: in_sing.(n2)); out_sing.(n1)<- ((List.nth nvarst index) :: out_sing.(n1)))
      transformersmap;
    in_sing, out_sing


  (*MAKE LOOP_COUNTER AT LEAST 1.... but does this enforce other things must transition?....YOU NEED TO IMPLEMENT THE RESET SHIT*)
  let closure_of_an_scc srk tr_symbols loop_counter vass =
    let label, graph, alphas, invars, invarmaxk = vass.label, vass.graph, vass.simulation, vass.invars, vass.invarmaxk in
    let simulation = alphas in
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
    let nvarst = map_terms srk (Mvass.create_n_vars srk (List.length transformers) [] "N") in
    let (form, (equiv_pairst, kvarst, svarst, rvarst)) =
      exp_base_helper srk tr_symbols loop_counter simulation transformers invars invarmaxk in
    let sum_n_eq_loop_counter = Mvass.exp_nvars_eq_loop_counter srk nvarst loop_counter in
    let ks_less_than_ns = Mvass.exp_kvarst_less_nvarst srk nvarst kvarst in
    let reachable_transitions = Mvass.get_reachable_trans graph in
    let post_conds_const = Mvass.exp_post_conds_on_transformers srk label transformersmap reachable_transitions nvarst alphas tr_symbols loop_counter in

    let in_sing, out_sing  = exp_compute_trans_in_out_index_numbers transformersmap (Array.length label) nvarst in
    let ests = Mvass.create_es_et srk (Array.length label) in
    let flow_consv_req = Mvass.exp_consv_of_flow srk in_sing out_sing ests in
    let in_out_one = Mvass.exp_one_in_out_flow srk ests nvarst in
    let ests_one_or_zero = Mvass.exp_each_ests_one_or_zero srk ests in
    let pre_post_conds = Mvass.exp_pre_post_conds srk ests label tr_symbols in
    let pos_constraints = create_exp_positive_reqs srk [nvarst; fst (List.split ests); snd (List.split ests)] in
    let form = mk_and srk [form; sum_n_eq_loop_counter; ks_less_than_ns; flow_consv_req; in_out_one;
                           ests_one_or_zero; pre_post_conds; pos_constraints; post_conds_const] in
    Log.errorf " Current D VAL %a" (Formula.pp srk) form;
    form



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

  (*Assumes that no vasses in the ordering are TOP *)
  let closure_of_an_ordering srk syms loop_counter ordering sccsclosure subloop_counters sccgraph symmappings formula : 'a formula =
    if (valid_ordering ordering sccgraph = false) then (mk_false srk)
    else(
      let rec make_closure_helper ordering =
        match ordering with
        | [] -> assert false
        | [hd] -> assert false(*[postify srk (merge_mappings syms symmappings.(hd) false true) sccsclosure.(hd)]*)
        | hd :: hdd :: hddd :: tl -> let tempform =(postify srk (merge_mappings syms symmappings.(hdd) true true) 
                               (postify srk (merge_mappings syms symmappings.(hd) false false) formula)) in
          Log.errorf "THE INBETWEEN FORMULA IS %a" (Formula.pp srk) tempform;
          tempform :: (postify srk (merge_mappings syms symmappings.(hdd) false true) 
                               (postify srk (merge_mappings syms symmappings.(hdd) true false) sccsclosure.(hdd)))
                             :: (make_closure_helper (hdd :: hddd :: tl))
        | [hd; hdd] -> let tempform =(postify srk (merge_mappings syms symmappings.(hdd) true true) 
                                        (postify srk (merge_mappings syms symmappings.(hd) false false) formula)) in
          Log.errorf "THE ORIG SCC FORM WAS %a" (Formula.pp srk) (sccsclosure.(hdd));
          Log.errorf "THE NEW SCC FORM WAS %a" (Formula.pp srk) (postify srk (merge_mappings syms symmappings.(hdd) false true)  sccsclosure.(hdd));

          tempform :: [(postify srk (merge_mappings syms symmappings.(hdd) false true)  sccsclosure.(hdd))]

      in
      let make_closure ordering =
        match ordering with
        | [] -> assert false
        | [hd] -> (*postify srk (marge_mappings symmappings.(hdd) syms false true)
                    postify srk (merge_mappings symmappings.(hd) syms true false) sccsclosure.(hd)*)
          Log.errorf "YOLENTA %d" hd;sccsclosure.(hd)
        | hd :: hdd :: tl ->
          (*mk_and srk [postify srk (merge_mappings.(hdd) syms false true) sccsclosure.(hd); make_closure_helper ordering]*)
          mk_and srk ((postify srk (merge_mappings syms symmappings.(hd) true false) sccsclosure.(hd)) :: (make_closure_helper ordering))
      in
      let rec make_add_loop_counters ordering =
        match ordering with
        | [] -> []
        | hd :: tl -> subloop_counters.(hd) :: (make_add_loop_counters tl)
      in
      mk_and srk [mk_eq srk (mk_add srk 
                               ((mk_real srk (QQ.of_int ((List.length ordering) - 1))) 
                                :: make_add_loop_counters ordering)) 
                    loop_counter;
                  make_closure ordering]
    )


  let exp srk syms loop_counter sccsform =
    let contains_top = BatArray.fold_left (fun acc vass ->
        if(M.nb_rows (unify (vass.simulation)) = 0) then true else acc) false sccsform.vasses in
    if contains_top then mk_true srk else(
      let scclabels = BatArray.map (fun scc -> mk_or srk (BatArray.to_list scc.label)) sccsform.vasses in
      let sccgraph = compute_edges srk syms scclabels sccsform.formula in
      let order = List.rev (BGraphTopo.fold (fun v acc -> Log.errorf "THIS SCC REACHED %d" v; v :: acc) sccgraph []) in
      let orderedsets = List.tl (List.rev (sublists order)) in
      (* CHECK IF ANY VASS IS TOP HERE*)
      let subloop_counters = BatArray.mapi (fun ind1 scc ->
          mk_const srk ((mk_symbol srk ~name:("counter_"^(string_of_int ind1)) `TyInt))) sccsform.vasses in
      let symmappings = BatArray.mapi (fun ind1 scc ->
          List.rev
            (BatList.fold_lefti (fun acc ind2 (x, x') ->
                 ((mk_symbol srk ~name:("x_"^(string_of_int ind1)^","^(string_of_int ind2)) `TyReal),
                  (mk_symbol srk ~name:("x'_"^(string_of_int ind1)^","^(string_of_int ind2)) `TyReal)) :: acc) [] syms)) sccsform.vasses
      in
      (* MAKE SUB LOOP COUNTERS POS*)
      let sccclosures = BatArray.mapi (fun ind vass -> closure_of_an_scc srk syms subloop_counters.(ind) vass) sccsform.vasses in
      let sub_loops_geq_0 = create_exp_positive_reqs srk [Array.to_list subloop_counters] in
      Log.errorf "Ordered sets size: %d" (List.length orderedsets);
      (*let orderedsets = [List.nth orderedsets 2] in*) (*2 is bad*)

      let form =
        List.fold_left (fun acc orderedset ->
            closure_of_an_ordering srk syms loop_counter orderedset sccclosures subloop_counters sccgraph symmappings sccsform.formula :: acc) [] orderedsets in
      let result = mk_and srk [sub_loops_geq_0; mk_or srk form] in
      (*let result = mk_and srk [sccclosures.(1); sub_loops_geq_0; mk_eq srk subloop_counters.(1) loop_counter] in*)
      Log.errorf "Final EXP is %a" (Formula.pp srk) result;
      result
    )




  let join _ _ _ _ = assert false
  let widen _ _ _ _ = assert false
  let equal _ _ _ _ = assert false


end

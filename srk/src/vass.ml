open Syntax
open BatPervasives
open Mdvas
module V = Linear.QQVector
module M = Linear.QQMatrix
module Z = Linear.ZZVector
module Q = Quantifier
module Int = SrkUtil.Int
module Accelerate =
  Iteration.MakeDomain(Iteration.Product(Iteration.LinearRecurrenceInequation)
                         (Iteration.PolyhedronGuard))
include Log.Make(struct let name = "srk.vass" end)




module Vassnew = struct

  (* sccvass is a vass abstraction such that
   * the control states (vertices) form a strongly connected
   * component.
   * graph[i][j] contains the set of vas transformers from
   * control state i to control state j (empty if no edge).
   * vas transformers must overapproximate transitions from 
   * transition states that model i to transition states that model 
   * j when s_lst is used as lin simulation.
   *
   * s_lst (simulation list), invars, and guarded_system are
   * defined as in mdvas:
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
   * invars is a list of invariants that hold after a single
   * transition, and every transition thereafter. invars is
   * used to remove variables from the formula.
   *
   * There are certain invariants that, 
   * when taken together, restrict
   * the transition system to running at most once
   * (for example, x' = 1 and x = x + 1). guarded_system is
   * true if any of these pairs of invariants exist.
   *)
  type 'a sccvas = 
    { label : ('a formula) array;
      graph : vas array array;
      simulation : M.t list;
      invars : 'a formula list;
      guarded_system : bool
    }

  (* vasses are the set of maximal sccvass
   * that can be formed for the derived control states
   *
   * formula is the initial formula used for this abstract
   * interpretation procedure (consider replacing with affine hull)
   *
   * sink is the end state; all paths in closure must terminate here.
   * Must at least overapproximate possible "post-states".
   *
   * skolem_constants...
   *)
  type 'a t = {
    vasses : 'a sccvas array;
    formula : 'a formula;
    sink : 'a formula;
    skolem_constants : Symbol.Set.t
  }


  (* Adjacency matrix with boolean true in g[i][j] if
   * edge from i to j.*)
  module BoolGraph = struct
    type t = bool array array
    module V = Int
    let is_directed = true
    let iter_vertex f g =
      BatEnum.iter f (0 -- (Array.length g - 1))
    let iter_succ f g v = Array.iteri (fun ind ele -> if ele then f ind ) g.(v)
    let fold_vertex f g a = BatEnum.fold (fun acc v -> f v acc) a (0 -- (Array.length g - 1))
    let fold_succ f g v a = BatArray.fold_righti 
        (fun ind ele acc -> if ele then f ind acc else acc) g.(v) a
  end
  (* Adjacency matrix; g[i][j] has set of vas transformers
   * v which represent transformers that can be taken from i to j*)
  module VassGraph = struct
    type t = vas array array
    module V = Int
    let is_directed = true
    let iter_vertex f g =
      BatEnum.iter f (0 -- (Array.length g - 1))
    let iter_succ f g v = Array.iteri 
        (fun ind ele -> if not (TSet.is_empty ele) then f ind ) g.(v)
    let fold_vertex f g a = BatEnum.fold (fun acc v -> f v acc) a (0 -- (Array.length g - 1))
    let fold_succ f g v a = BatArray.fold_righti 
        (fun ind ele acc -> if not (TSet.is_empty ele) then f ind acc else acc) g.(v) a
  end

  module BGraphComp = Graph.Components.Make(BoolGraph)
  module BGraphTrav = Graph.Traverse.Dfs(BoolGraph)
  module BGraphTopo = Graph.Topological.Make(BoolGraph)
  module GraphComp = Graph.Components.Make(VassGraph) 
  module GraphTrav = Graph.Traverse.Dfs(VassGraph)



  let map_terms srk = List.map (fun (var : Syntax.symbol) -> mk_const srk var)


  let ident_matrix_real n =
    BatList.fold_left (fun matr dim  ->
        M.add_entry dim dim (QQ.of_int 1) matr) M.zero (BatList.of_enum (0--n))

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



  (*Determine if there exists a transition from cs1 to cs2
   * using transition system phi*)
  let exists_transition srk cs1 cs2 tr_symbols phi =
    let solver = Smt.mk_solver srk in
    Smt.Solver.reset solver;
    let formula =  mk_and srk [cs1; postify srk tr_symbols cs2; phi] in
    Smt.Solver.add solver [formula];
    match Smt.Solver.get_model solver with
    | `Unsat -> false
    | `Unknown -> true
    | `Sat _ -> true

  (*Compute boolean adjacency graph of control states for transition system phi*)
  let compute_edges srk tr_symbols c_states phi =
    let graph = Array.make_matrix (Array.length c_states) (Array.length c_states) false in
    BatArray.iteri (fun ind1 arr ->
        BatArray.modifyi (fun ind2 _ ->
            exists_transition srk c_states.(ind1) c_states.(ind2) tr_symbols phi)
          arr)
      graph;
    graph


  (*TODO: make pretty print prettier*)
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

  (*Computes vass for a given list of control states and formula*)
  let compute_single_scc_vass ?(exists=fun x -> true) srk tr_symbols labels_lst phi =
    (* Restrict phi to configurations that model a control state *)
    let postified_labels = List.map (fun lbl -> postify srk tr_symbols lbl) labels_lst in
    let phi' = mk_and srk [mk_or srk labels_lst; mk_or srk postified_labels; phi] in
    let phi'',invars, guarded_system = find_invariants srk tr_symbols phi' in
    (*pre_graph represents adjacency (transformers, sim) graph for control states
     * prior to converting all cells of graph to use same sim matrix*)
    let pre_graph = BatArray.init 
        (List.length labels_lst) 
        (fun _ -> (BatArray.init 
           (List.length labels_lst) 
           (fun _ -> (TSet.empty,[]))))
    in
    (*Populate graph with transformers between two control states*)
    BatArray.iteri (fun ind1 arr ->
        BatArray.modifyi (fun ind2 _ ->
            let {v; s_lst} = abstract ~exists srk tr_symbols
                (mk_and srk 
                   [(List.nth labels_lst ind1); 
                    postify srk tr_symbols (List.nth labels_lst ind2); 
                    phi'']) 
            in
            (v, s_lst))
          arr
      ) pre_graph; 
    (* Computes list of lin transformation that determines
     * how to transform each cell of pregraph to use same sim matrix
     * Also computes the sim matrix that will be used *)
    let imglist, s_lst = BatArray.fold_left 
        (fun (imglst, s_lst) arr ->
           BatArray.fold_left 
             (fun (imglist, s_lst) (_, pregraph_s_lst) ->
                let r1, r2, s_lst' = coprod_find_transformation s_lst pregraph_s_lst in
                (r1, r2) :: imglist, s_lst') 
             (imglst, s_lst) arr) 
        ([], [ident_matrix_syms srk tr_symbols]) pre_graph
    in
    (*Will hold transformer adjacency graph such that each cell uses same sim matrix*)
    let graph = BatArray.init 
        (List.length labels_lst) 
        (fun _ -> 
           (BatArray.init (List.length labels_lst) 
              (fun _ -> (TSet.empty))))
    in
    let rec apply_images base_img imglist ind1 ind2 =
      match imglist with
      | (r1, r2) :: tl ->
        let r1 = unify r1 in
        let r2 = unify r2 in
        let r1' = M.mul base_img r1 in
        let r2' = M.mul base_img r2 in
        let (v, _) = pre_graph.(ind1).(ind2) in
        let v' = coprod_compute_image v [r2'] in
        graph.(ind1).(ind2)<-v';
        let ind1', ind2' = if ind2 = 0 then ind1 - 1, (List.length labels_lst) - 1
          else ind1, ind2 - 1 in
        apply_images r1' tl ind1' ind2'
      | [] -> ()
    in
    (*TODO: 100 is magic number. should be something like largest s*)
    apply_images (ident_matrix_real 100) imglist 
      ((List.length labels_lst) - 1) ((List.length labels_lst) - 1);
    {label=Array.of_list labels_lst;graph;simulation=s_lst;invars;guarded_system}

  (* Project a formula onto the symbols that satisfy the "exists"
     predicate, and convert to DNF *)
  let project_dnf srk exists phi =
    let phi =
      rewrite srk ~down:(nnf_rewriter srk) phi
      |> SrkSimplify.simplify_terms srk
    in
    let solver = Smt.mk_solver srk in
    Smt.Solver.add solver [phi];
    let rec go cubes =
      match Smt.Solver.get_model solver with
      | `Unsat -> cubes
      | `Unknown -> assert false
      | `Sat m ->
        match Interpretation.select_implicant m phi with
        | None -> assert false
        | Some imp ->
          let cube =
            Q.local_project_cube srk exists m imp
            |> SrkSimplify.simplify_conjunction srk
            |> mk_and srk
          in
          Smt.Solver.add solver [mk_not srk cube];
          go (cube :: cubes)
    in
    go []

  (*Given a set of control, combine control states that overlap*)
  let get_largest_polyhedrons srk control_states =
    let rec intersect_ele non_intersect ele unchecked changed =
      match unchecked with
      | [] -> non_intersect, ele, changed
      | hd :: tl ->
        let solver = Smt.mk_solver srk in
        let phi = (rewrite srk ~down:(nnf_rewriter srk) (mk_and srk [ele; hd])) in 
        Smt.Solver.add solver [phi];
        match Smt.Solver.get_model solver with
        | `Unsat -> intersect_ele (hd :: non_intersect) ele tl changed
        | `Unknown -> assert false
        | `Sat m -> intersect_ele non_intersect (mk_or srk [ele; hd]) tl true
    in

    let rec loop_states front back =
      match back with
      | [] -> front
      | hd :: tl ->
        let back', ele, changed = intersect_ele [] hd tl false in
        if changed = true 
        then loop_states front (ele :: back')
        else loop_states (ele :: front) back'
    in
    loop_states [] control_states

  (*Compute control states using projection to pre transition states.
   * Also compute sink*)
  let get_control_states ?(exists=fun x -> true) srk tr_symbols phi =
    let pre_symbols = pre_symbols tr_symbols in
    let post_symbols = post_symbols tr_symbols in
    let exists_pre x =
      exists x && not (Symbol.Set.mem x post_symbols)
    in
    let exists_post x =
      exists x && not (Symbol.Set.mem x pre_symbols)
    in
    let control_states = project_dnf srk exists_pre phi in
    (*sink can also just be true given while exact phi used as transition to sink*)
    let sink = mk_or srk (project_dnf srk exists_post phi) in 
    let control_states' = get_largest_polyhedrons srk control_states in
    BatArray.of_list control_states', sink


  let abstract ?(exists=fun x -> true) srk tr_symbols phi =
    let skolem_constants = Symbol.Set.filter (fun a -> not (exists a)) (symbols phi) in
    let phi = Nonlinear.linearize srk (rewrite srk ~down:(nnf_rewriter srk) phi) in
    let control_states, sink = get_control_states ~exists srk tr_symbols phi in
    let graph = compute_edges srk tr_symbols control_states phi in
    let num_sccs, func_sccs = BGraphComp.scc graph in
    let sccs = Array.make num_sccs  [] in
    BatArray.iteri (fun ind lab -> sccs.(func_sccs ind)<-(lab :: sccs.(func_sccs ind)))
      control_states;
    if num_sccs = 0 then
      {vasses= BatArray.init 0 (fun x -> assert false); 
       formula=phi; skolem_constants; sink=sink}
    else(
      let vassarrays = BatArray.map 
          (fun scc -> compute_single_scc_vass ~exists srk tr_symbols scc phi) sccs in
      let result = {vasses=vassarrays;formula=phi; skolem_constants; sink=sink} in
      logf ~level:`always "%a" (pp srk tr_symbols) result;
      result
    )


  (*Create array of list of indices of transformers going in and
   * out of each single control state*)
  let get_incoming_outgoing_edges transformersmap num_cs =
    let entry, exit = Array.make num_cs [], Array.make num_cs [] in
    List.iteri (fun index (n1, trans, n2) -> 
        entry.(n2)<-(index :: entry.(n2)); exit.(n1)<- (index :: exit.(n1)))
      transformersmap;
    entry, exit


  (*either node is local source/sink or is not*)
  let exp_each_ests_one_or_zero srk local_s_t =
    (*This redundant condition seems to reduce runtime for more complex cases*)
    if (List.length local_s_t = 1) then
      (
        let (source, sink) = List.hd local_s_t in
        mk_and srk [mk_eq srk source (mk_one srk); mk_eq srk sink (mk_one srk)]
      )
    else(
      mk_and srk
        (List.map (fun (source, sink) -> 
             mk_and srk
               [mk_or srk [mk_eq srk source (mk_zero srk); mk_eq srk source (mk_one srk)];
                mk_or srk [mk_eq srk sink (mk_zero srk); mk_eq srk sink (mk_one srk)]])
            local_s_t))

  (* Requires entry and exit point *)
  let split_terms_add_to_one srk local_s_t = 
    let source,sink = List.split local_s_t in
      mk_and srk 
        [mk_eq srk (mk_add srk source) (mk_one srk);
         mk_eq srk (mk_add srk sink) (mk_one srk)]



  let upper_bound_terms srk terms upper_bound = 
    mk_and srk  (BatList.map 
                   (fun var -> mk_and srk 
                       [mk_leq srk (mk_zero srk) var;
                        mk_leq srk var (mk_real srk (QQ.of_int upper_bound))]) 
                   terms)


  (*Distance is 0 if and only if source label; reset taken version*)
  let set_flow_source_from_reset srk distvars entry reset_trans =
    mk_and srk (BatList.mapi
                  (fun ind distvar ->
                     if (BatList.mem reset_trans entry.(ind))
                     then (mk_eq srk distvar (mk_zero srk))
                     else (mk_not srk (mk_eq srk distvar (mk_zero srk))))
                  distvars)



  (*Distance is 0 if and only if source label; reset not taken version*)
  let set_flow_source srk distvars sources =
    mk_and srk (BatList.mapi
                  (fun ind distvar ->
                     mk_iff 
                       srk 
                       (mk_eq srk (List.nth sources ind) (mk_one srk))
                       (mk_eq srk distvar (mk_zero srk)))
                  distvars)


  (*For all control states, if is not source and there is a path from source with flow and
   * (dist < n), then there is flow on an edge to control state
   * originating from a node with dist - 1*)
  let dist_vars_path srk distvars transformer_w_ends coh_class_kvars entry =
    mk_and srk (BatList.mapi 
                  (fun ind var ->
                     mk_if srk 
                       (mk_and srk
                          [mk_lt srk (mk_zero srk) var;
                           mk_lt srk var (mk_real srk (QQ.of_int (List.length distvars)))])
                       (mk_or srk
                          (List.fold_left
                             (fun acc ele ->
                                let (pred, _, _) = List.nth transformer_w_ends ele in
                                (mk_and srk
                                   [mk_leq srk (mk_one srk) (List.nth coh_class_kvars ele);
                                    mk_eq srk 
                                      (mk_add srk [(List.nth distvars pred); (mk_one srk)])
                                      var]) 
                                :: acc)
                             [mk_false srk] 
                             entry.(ind))))
                  distvars)


  (*If dist from source = inf (n), then no outgoing flow allowed*)
  let dist_inf_constr srk distvars local_s_t entry exit coh_class_kvars =
    mk_and srk 
      (BatList.mapi
         (fun ind var ->
            let (_,sink) = List.nth local_s_t ind in
            let entry_this = List.map (fun ind -> List.nth coh_class_kvars ind) entry.(ind)
            in
            let exit_this = List.map (fun ind -> List.nth coh_class_kvars ind) exit.(ind) in
            mk_if srk
              (mk_eq srk var (mk_real srk (QQ.of_int (List.length distvars))))
              (mk_and srk
                 (List.map 
                    (fun term -> mk_eq srk (mk_zero srk) term) 
                    (sink :: (entry_this @ exit_this)))))
         distvars)


  (* Generates consv of flow constraints for each individual label and a given coh classes
   * transformers, assuming that flow starts on the active local source *) 
  let consv_of_flow srk entry exit local_s_t coh_class_kvars =
    let entry_kvars = BatArray.map 
        (fun indlist -> List.map (fun ind -> List.nth coh_class_kvars ind) indlist) entry in
    let exit_kvars = BatArray.map 
        (fun indlist -> List.map (fun ind -> List.nth coh_class_kvars ind) indlist) exit in 
    mk_and srk
      (List.mapi (fun ind (source, sink) ->
           mk_eq srk
             (mk_add srk (source  :: entry_kvars.(ind)))
             (mk_add srk (sink :: exit_kvars.(ind))))
          local_s_t)

  (* Generates consv of flow constraints for each individual label and a given coh classes
   * transformers, assuming that flow starts on transformer reset_trans *)
  let consv_of_flow_after_last_reset srk entry exit local_s_t coh_class_kvars reset_trans =
    let entry_kvars = BatArray.map 
        (fun indlist -> List.map (fun ind -> List.nth coh_class_kvars ind) indlist) entry in
    let exit_kvars = BatArray.map 
        (fun indlist -> List.map (fun ind -> List.nth coh_class_kvars ind) indlist) exit in
    mk_and srk
      (List.mapi (fun ind (_, sink) ->
           mk_eq srk
             (mk_add srk 
                ((if (BatList.mem reset_trans entry.(ind)) 
                  then mk_one srk 
                  else mk_zero srk) :: entry_kvars.(ind)))
             (mk_add srk (sink :: exit_kvars.(ind))))
          local_s_t)



  (* The last reset for a given coh class determines the starting values for that
   * dimensions of that coh class, the entry point for that coh class flow, and 
   * a restriction that all coh class reset prior to this coh class must've taken
   * the transformer this coh class was reset on. This function generates those
   * constraints for a single coh class*)
  let last_reset_constr_coh_class srk rvar ksum ksums svar_dim_pairs 
      transformers kvars_coh_classes unified_s tr_symbols coh_class_kvars entry
      exit local_s_t coh_class_dist_vars =
    mk_or srk
      (* The coh class was never reset. Set the coh class reset indicator var to -1,
       * Configure entry point for coh class flow. Set init val for lin terms of 
       * coh class equal to val of lin terms at start of program execution.
       * Consv of coh class flow taken care of by convs of master flow, 
       * in another part of program. *)
      ((mk_and srk
          (mk_eq srk rvar (mk_real srk (QQ.of_int (-1))) ::
           set_flow_source srk coh_class_dist_vars (fst (List.split local_s_t)) :: 
           (List.map
              (fun (svar, dim) -> 
                 mk_eq srk svar 
                   (preify srk tr_symbols (Linear.of_linterm srk (M.row dim unified_s))))
              svar_dim_pairs)))
       (* The coh class was reset at some point. Set coh class reset indicator to
        * denote transformer # last reset occured at. Set constraints for consv of coh
        * class flow and starting point of coh class flow. Require that coh classes
        * whose last reset occured earlier to this coh class last reset used the transformer
        * that this coh class reset on. Set init val for lin terms of coh class to val
        * at last reset*)
       :: (BatList.mapi 
             (fun ind {a; b} ->
                if ZZ.equal (Z.coeff (snd (List.hd svar_dim_pairs)) a) ZZ.one 
                then (mk_false srk)
                else (
                  mk_and srk
                    (consv_of_flow_after_last_reset srk entry exit local_s_t 
                       coh_class_kvars ind ::
                     (mk_eq srk rvar (mk_real srk (QQ.of_int ind))) ::
                     exp_other_reset_helper srk ksum ksums kvars_coh_classes ind ::
                     set_flow_source_from_reset srk coh_class_dist_vars entry ind :: 
                     (List.map
                        (fun (svar, dim) -> 
                           mk_eq srk svar (mk_real srk (V.coeff dim b))) svar_dim_pairs)))) 
             transformers))


  (*For each coh class, set constraints  relating to the transformer on which this coh
   * class takes last reset. Includes setting reset indicator var for coh class,
   * setting init values for coh class dims, and setting up coh class flow constraints.
   * *)
  let coh_classes_last_reset_constr srk coh_class_pairs transformers kvars_coh_classes ksums
      unified_s tr_symbols entry exit local_s_t coh_classes_dist_vars num_cs 
      transformer_w_ends =
    mk_and srk
      (List.mapi (fun ind (coh_class_kvars, svarstdims, rvar, ksum) ->
           mk_and srk [
             upper_bound_terms srk (List.nth coh_classes_dist_vars ind) num_cs;
             dist_vars_path srk (List.nth coh_classes_dist_vars ind) transformer_w_ends
               coh_class_kvars entry;
             dist_inf_constr srk (List.nth coh_classes_dist_vars ind) local_s_t entry exit
               coh_class_kvars; 
             last_reset_constr_coh_class srk rvar ksum ksums svarstdims transformers
               kvars_coh_classes unified_s tr_symbols coh_class_kvars entry exit local_s_t 
               (List.nth coh_classes_dist_vars ind)])
          coh_class_pairs)


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

  (*Compute the condition that must hold if a given transformer is taken... Confirm correctness of this*)
  let compute_trans_post_cond srk prelabel postlabel (trans : transformer) (rtrans,rverts) alphas tr_symbols ind = 
    let term_list = term_list srk alphas tr_symbols in
    let f' = mk_or srk (List.map (fun ele -> gamma_transformer srk term_list ele) (TSet.elements rtrans)) in
    let pre_symbols = pre_symbols tr_symbols in
    let man = Polka.manager_alloc_strict () in
    let exists_post x = not (Symbol.Set.mem x pre_symbols) in
    let trans' = gamma_transformer srk term_list trans in
    let ptrans_form = (mk_and srk [prelabel;trans';postlabel]) in
    let post_trans = SrkApron.formula_of_property (Abstract.abstract ~exists:exists_post srk man ptrans_form) in
    let lri_form = (rewrite srk ~down:(nnf_rewriter srk) f') in 
    let rslt = SrkApron.formula_of_property
        (Abstract.abstract ~exists:exists_post srk man
           (mk_and srk
              [preify srk tr_symbols post_trans;
               Accelerate.closure (Accelerate.abstract srk tr_symbols lri_form)]))
    in
    rslt


  (* If a transformers is taken, that transformer post condition must hold*)
  let exp_post_conds_on_transformers srk label transformersmap reachability nvarst alphas tr_symbols =
    mk_and srk 
      (BatList.mapi (fun ind (n1, trans, n2) -> 
           let post_cond = compute_trans_post_cond srk label.(n1) (postify srk tr_symbols label.(n2)) 
               trans reachability.(n2) alphas tr_symbols ind in
           mk_if srk (mk_lt srk (mk_zero srk) (List.nth nvarst ind)) post_cond) transformersmap
      )


  let closure_of_an_scc srk tr_symbols loop_counter vass =
    let label, graph, alphas, invars, guarded_system = vass.label, vass.graph, vass.simulation, vass.invars, vass.guarded_system in
    let simulation = alphas in

    let ests = create_es_et srk (Array.length label) in
    let in_out_one = split_terms_add_to_one srk ests in
    let ests_one_or_zero = exp_each_ests_one_or_zero srk ests in
    let pre_post_conds = exp_pre_post_conds srk ests label tr_symbols in
    let pos_constraints_1 = create_exp_positive_reqs srk [fst (List.split ests); snd (List.split ests)] in
    let invariants = mk_or srk [mk_eq srk loop_counter (mk_zero srk);
                                mk_and srk invars] in
    let gs_constr = if guarded_system 
      then (mk_leq srk loop_counter (mk_one srk)) 
      else mk_true srk in  




    (*If case is top localized to one scc; still require that a label is used*)
    if(M.nb_rows (unify (vass.simulation)) = 0) then
      ((mk_and srk [in_out_one; ests_one_or_zero; pre_post_conds(*; pos_constraints_1*);
                    invariants; gs_constr]), (fst (List.split ests)))
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
      let entvars = map_terms srk (create_n_vars srk (Array.length label) [] "ENT") in
      let ent_equiv_class_vars = BatList.mapi (fun ind _ ->  map_terms srk (create_n_vars srk (Array.length label) [] ("ENTC"^(string_of_int ind)))) alphas in


      let (form, (equiv_pairst, kvarst, ksumst)) =
        exp_base_helper srk tr_symbols loop_counter simulation transformers in
      let sum_n_eq_loop_counter = exp_nvars_eq_loop_counter srk nvarst loop_counter in
      let ks_less_than_ns = exp_kvarst_less_nvarst srk nvarst kvarst in
      let reachable_transitions = get_reachable_trans graph in
      let post_conds_const = exp_post_conds_on_transformers srk label 
          transformersmap reachable_transitions nvarst alphas tr_symbols in
      let in_sing, out_sing  = get_incoming_outgoing_edges 
          transformersmap (Array.length label) in
      let flow_consv_req = consv_of_flow srk in_sing out_sing ests nvarst in
      let pos_constraints = create_exp_positive_reqs srk [nvarst] in
      let sx_constraints = coh_classes_last_reset_constr srk equiv_pairst transformers (nvarst:: kvarst) 
          ((mk_add srk nvarst) :: ksumst) (unify alphas) tr_symbols in_sing out_sing
          ests ent_equiv_class_vars (Array.length label) transformersmap in
      let ent_bounds = upper_bound_terms srk entvars (Array.length label) in
      let ent_source = set_flow_source srk entvars (fst (List.split ests)) in
      let ent_non_source = dist_vars_path srk entvars transformersmap nvarst in_sing in
      let ent_max = dist_inf_constr srk entvars ests in_sing out_sing nvarst in 
      let form = mk_and srk [form; sum_n_eq_loop_counter; ks_less_than_ns; flow_consv_req; in_out_one;
                             ests_one_or_zero; pre_post_conds; pos_constraints; pos_constraints_1; post_conds_const; sx_constraints;
                             ent_bounds; ent_source; ent_non_source; ent_max; invariants;
                             gs_constr] in
      form, (fst (List.split ests)))

  (*Take (x, x') list and (y, y') list and make a list that combine in some way*)
  let merge_mappings pre post use_pres_post use_posts_pre =
    BatList.fold_left2 (fun acc (x, x') (y, y') -> 
        if use_posts_pre then (
          if use_pres_post then (x',  y) :: acc
          else (x, y) :: acc
        )
        else if use_pres_post then (x', y') :: acc
        else (x, y') :: acc) [] pre post

  (*If no trans is taken, vars do not change; loop counter is 0*)
  let no_trans_taken srk loop_counter syms =
    let eqs = (List.map (fun (x, x') -> mk_eq srk (mk_const srk x) (mk_const srk x'))) syms in
    mk_and srk ((mk_eq srk loop_counter (mk_zero srk)) :: eqs)

  (*Bound each scc ordering var by 0 and max number sccs*)
  let ordering_bounds srk ordering_vars max =
    mk_and srk (BatArray.to_list (BatArray.map (fun var -> mk_and srk 
                                                   [mk_leq srk (mk_zero srk) var;
                                                    mk_lt srk var max]) ordering_vars))

  (*No duplicates in the scc ordering vars*)
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


  (*Requirements for composition of scc components*)
  let come_next_req srk ordering_vars es loop_counters num_scc_used scc_closures symmappings syms formula skolemmappings =
    mk_and srk (BatList.flatten (BatArray.to_list (BatArray.mapi (fun ind1 o_var1 ->
        BatArray.to_list (BatArray.mapi (fun ind2 o_var2 ->
            if ind1 <> ind2 then(
              (*If o_vari immediatly precedes o_varj: if scci is off, then sccj must be too. Otherwise,
               * Sccj is off and max sccs used is o_vari, or sccj is used, is linked to scci, and at least o_varj
               * sccs are used*)
              mk_if srk (mk_eq srk o_var1 (mk_sub srk o_var2 (mk_one srk)))
                (mk_ite srk (mk_eq srk (mk_add srk es.(ind1)) (mk_zero srk))
                   (mk_and srk [(mk_eq srk (mk_add srk es.(ind2)) (mk_zero srk));
                                mk_eq srk loop_counters.(ind2) (mk_zero srk)])
                   (mk_or srk [(mk_and srk [(mk_eq srk (mk_add srk es.(ind2)) (mk_zero srk));
                                            mk_eq srk loop_counters.(ind2) (mk_zero srk);
                                            mk_eq srk num_scc_used o_var1]);
                               mk_and srk [scc_closures.(ind2);
                                           (postify srk skolemmappings.(ind1)
                                              (postify srk (merge_mappings syms symmappings.(ind2) true true) 
                                                 (postify srk (merge_mappings syms symmappings.(ind1) false false) formula)));
                                           mk_leq srk o_var2 num_scc_used]])))
            else (mk_true srk))
            ordering_vars)) ordering_vars)))

  (*Require first scc to be used; link up init x values to this scc*)
  let first_scc_used srk ordering_vars es sccs_closures symmappings syms =
    mk_and srk (BatArray.to_list (BatArray.mapi (fun ind1 o_var1 ->
        mk_if srk (mk_eq srk o_var1 (mk_zero srk))
          (mk_and srk (mk_eq srk (mk_add srk es.(ind1)) (mk_one srk) :: sccs_closures.(ind1) ::
                       (BatList.map2 (fun (x, x') (sccx, sccx') -> mk_eq srk (mk_const srk x) (mk_const srk sccx))
                          syms symmappings.(ind1))))) ordering_vars))

  (*If scci comes before sccj in topological sort, but sccj comes before scci in scc ordering, scci must be 0*)
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
    (*No sccs means no labels found mean no transitions exist*)
    if BatArray.length sccsform.vasses = 0 then (no_trans_taken srk loop_counter syms) else(
      let sink = sccsform.sink in
      let doublex' = List.map (fun (x, x') -> (x', x')) syms in
      let symmappings = BatArray.mapi (fun ind1 scc ->
          List.rev
            (BatList.fold_lefti (fun acc ind2 (x, x') ->
                 ((mk_symbol srk ~name:((show_symbol srk x)^"_"^(string_of_int ind1)) (typ_symbol srk x)),
                  (mk_symbol srk ~name:((show_symbol srk x')^"_"^(string_of_int ind1)) (typ_symbol srk x'))) :: acc) [] syms))
          sccsform.vasses
      in
      let symmappings = BatArray.append symmappings (BatArray.make 1 doublex') in
      let subloop_counters = BatArray.mapi (fun ind1 scc ->
          mk_const srk ((mk_symbol srk ~name:("counter_"^(string_of_int ind1)) `TyInt))) symmappings in

      let skolem_mappings = BatArray.mapi (fun ind1 scc ->
          BatList.fold_left 
            (fun acc x -> (x, (mk_symbol srk ~name:((show_symbol srk x)^"_"^(string_of_int ind1)) (typ_symbol srk x))) 
                          :: acc)
            []
            (Symbol.Set.elements sccsform.skolem_constants))
          symmappings
      in
      let skolem_mappings_transitions = BatArray.mapi (fun ind1 scc ->
          BatList.fold_left 
            (fun acc x -> (x, (mk_symbol srk ~name:((show_symbol srk x)^"_"^(string_of_int ind1)) (typ_symbol srk x))) 
                          :: acc)
            []
            (Symbol.Set.elements sccsform.skolem_constants))
          symmappings
      in

      let sccclosures_es = BatArray.mapi (fun ind vass -> closure_of_an_scc srk syms subloop_counters.(ind) vass) sccsform.vasses in
      let sccclosures, es = BatList.split (BatArray.to_list sccclosures_es) in
      let sccclosures, es = BatArray.of_list sccclosures, BatArray.of_list es in
      (*We compute scc closure without scc specific x, x' and then add these in after closure*)
      let sccclosures = BatArray.append sccclosures (BatArray.make 1 sink) in
      let sccclosures = BatArray.mapi (fun ind closure ->  
          (postify srk skolem_mappings.(ind) 
             (postify srk (merge_mappings syms symmappings.(ind) false true) 
                (postify srk (merge_mappings syms symmappings.(ind) true false) closure))))
          sccclosures in
      Log.errorf "MAKE IT HERE";

      let es = BatArray.append es (BatArray.make 1 [(mk_real srk (QQ.of_int 1))]) in
      let scclabels = BatArray.map (fun scc -> mk_or srk (BatArray.to_list scc.label)) sccsform.vasses in		
      let sccgraph = compute_edges srk syms scclabels sccsform.formula in
      let num_scc_used = mk_const srk (mk_symbol srk ~name:("Num_scc_used") `TyInt) in
      let order = List.rev (BGraphTopo.fold (fun v acc -> Log.errorf "THIS SCC REACHED %d" v; v :: acc) sccgraph []) in
      let sub_loops_geq_0 = create_exp_positive_reqs srk [Array.to_list subloop_counters] in
      let scc_ordering_pre_sink = BatArray.mapi (fun ind1 scc ->
          mk_const srk ((mk_symbol srk ~name:("ordering_"^(string_of_int ind1)) `TyInt))) sccsform.vasses in
      let sink_ordering = mk_const srk (mk_symbol srk ~name:("ordering_SINK") `TyInt) in
      let scc_ordering = BatArray.append scc_ordering_pre_sink (BatArray.make 1 sink_ordering) in
      let order_bounds_const = ordering_bounds srk scc_ordering (mk_real srk (QQ.of_int (BatArray.length sccclosures))) in
      let no_dups_constr = no_dups_ordering srk scc_ordering in
      let come_next_const = come_next_req srk scc_ordering es subloop_counters num_scc_used sccclosures symmappings syms sccsform.formula skolem_mappings_transitions in
      let first_scc_const = first_scc_used srk scc_ordering es sccclosures symmappings syms in
      let num_scc_used_bound = mk_and srk 
          [mk_lt srk num_scc_used (mk_real srk (QQ.of_int (BatArray.length sccclosures)));
           mk_leq srk (mk_zero srk) num_scc_used] in
      let num_scc_used_sink = mk_eq srk num_scc_used sink_ordering in
      let loop_bound = mk_eq srk (mk_add srk (num_scc_used :: (BatArray.to_list subloop_counters))) loop_counter in
      let order_constr = topo_order_constraints srk order es scc_ordering in
      let result = mk_or srk [mk_and srk [order_bounds_const; sub_loops_geq_0; no_dups_constr; come_next_const; first_scc_const;
                                          num_scc_used_bound; num_scc_used_sink; loop_bound; mk_leq srk (mk_zero srk) loop_counter; order_constr];
                              no_trans_taken srk loop_counter syms] in
      Log.errorf "Done";
      result
    )



  let join _ _ _ _ = assert false
  let widen _ _ _ _ = assert false
  let equal _ _ _ _ = assert false


end

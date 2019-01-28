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
    formula : 'a formula;
    skolem_constants : Symbol.Set.t
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



  let compute_transformers_two_labels ?(exists=fun x -> true) srk symbols label1 label2 orig_form =
    let new_form =  (rewrite srk ~down:(nnf_rewriter srk) (mk_and srk [label1; postify srk symbols label2; orig_form])) in
    let (x''s, x''_forms) = 
      List.split (List.fold_left (fun acc (x, x') -> 
          let x'' = (mk_symbol srk (typ_symbol srk x)) in
          let x''_form = (mk_eq srk (mk_const srk x'') 
                            (mk_sub srk (mk_const srk x') (mk_const srk x))) in
          ((x'', x'), x''_form) :: acc) [] symbols) in
    let solver = Smt.mk_solver srk in
    let rec go vas count =
      assert (count > 0);
      Smt.Solver.add solver [mk_not srk (gamma srk vas symbols)];
      match Smt.Solver.get_model solver with
      | `Unsat -> vas
      | `Unknown -> assert false
      | `Sat m ->
        match Interpretation.select_implicant m new_form with
        | None -> assert false
        | Some imp ->
          let alpha_v = alpha_hat srk (mk_and srk imp) symbols x''s x''_forms false in
          go (coproduct srk vas alpha_v) (count - 1)
    in
    Smt.Solver.add solver [new_form];
    let {v;alphas} = go (mk_bottom srk symbols) 20 in
    let result = (v,alphas) in
    result



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





  let compute_single_scc_vass ?(exists=fun x -> true) srk tr_symbols labels_lst orig_form =
    Log.errorf "STARTED COMPUTATION FOR A SINGLE VASS";
    let postified_labels = List.map (fun lbl -> postify srk tr_symbols lbl) labels_lst in
    let formula = mk_and srk [mk_or srk labels_lst; mk_or srk postified_labels; orig_form] in
    let formula',invars, invarmaxk = find_invariants srk tr_symbols formula in
    (*Look into removing conunction of labels from formula' after invars calculated*)
    let pre_graph = BatArray.init 
        (List.length labels_lst) 
        (fun _ -> (BatArray.init 
           (List.length labels_lst) 
           (fun _ -> (TSet.empty,[]))))
    in
    BatArray.iteri (fun ind1 arr ->
        BatArray.modifyi (fun ind2 _ ->
            compute_transformers_two_labels ~exists srk tr_symbols (List.nth labels_lst ind1) (List.nth labels_lst ind2) formula')
          arr
      ) pre_graph;
    let imglist, alphas = BatArray.fold_left 
        (fun (imglst, alphas) arr ->
           BatArray.fold_left 
             (fun (imglist, alphas) (_, alphasele) ->
                let s1, s2, alphas' = coprod_find_images alphas alphasele in
                (s1, s2) :: imglist, alphas') (imglst, alphas) arr) ([], [ident_matrix_syms srk tr_symbols]) pre_graph
    in
     let graph = BatArray.make 
        (List.length labels_lst)
        (BatArray.make
           (List.length labels_lst)
           (TSet.empty))
    in
    let graph = BatArray.init 
        (List.length labels_lst) 
        (fun _ -> (BatArray.init 
                     (List.length labels_lst) 
                     (fun _ -> (TSet.empty))))
    in

    let rec apply_images base_img imglist ind1 ind2 =
      match imglist with
      | (s1, s2) :: tl ->
        let s1 = unify s1 in
        let s2 = unify s2 in
        let s1' = M.mul base_img s1 in
        let s2' = M.mul base_img s2 in
        let (v, _) = pre_graph.(ind1).(ind2) in
        let v' = coprod_use_image v [s2'] in
        Log.errorf "Ind1 is %d and ind2 is %d" ind1 ind2;
        Log.errorf "base image is %a" M.pp base_img;
        Log.errorf "S1 is %a" M.pp s1;
        Log.errorf "S2 is %a" M.pp s2;
        Log.errorf "S1' is %a" (M.pp) s1';
        Log.errorf "S2' is %a" (M.pp) s2';
        Log.errorf "Start show v";
        TSet.iter (fun t -> Log.errorf "a is %a" Z.pp t.a; Log.errorf "b is %a" V.pp t.b) v;
        Log.errorf "Start show v'";
        TSet.iter (fun t -> Log.errorf "a is %a" Z.pp t.a; Log.errorf "b is %a" V.pp t.b) v';
        graph.(ind1).(ind2)<-v';
        let ind1', ind2' = if ind2 = 0 then ind1 - 1, (List.length labels_lst) - 1
          else ind1, ind2 - 1 in
        Log.errorf "THIS IS TEMP END OF A SINGLE GRAPH UPDATE";
        BatArray.iteri (fun ind arr ->
            BatArray.iteri (fun ind2 trans ->
                Log.errorf "Num connections from label %d to label %d is: %d \n" ind ind2 (TSet.cardinal trans);
                TSet.iter (fun trans ->
                    Log.errorf "Label %d admits trans a: %a b: %a \n" ind (Z.pp) trans.a (V.pp) trans.b) trans) arr) graph;




        apply_images s1' tl ind1' ind2'
      | [] -> ()
    in
    apply_images (ident_matrix_real 100) imglist ((List.length labels_lst) - 1) ((List.length labels_lst) - 1); (*find actual ident here*)
    BatArray.iteri (fun ind arr ->
            BatArray.iteri (fun ind2 trans ->
            Log.errorf "Num connections from label %d to label %d is: %d \n" ind ind2 (TSet.cardinal trans);
                TSet.iter (fun trans ->
                    Log.errorf "Label %d admits trans a: %a b: %a \n" ind (Z.pp) trans.a (V.pp) trans.b) trans) arr) graph;
     
    {label=Array.of_list labels_lst;graph;simulation=alphas;invars;invarmaxk}






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

  (* Project a formula onto the symbols that satisfy the "exists"
     predicate, and convert to DNF *)
  let project_dnf srk exists formula =
    let formula =
      rewrite srk ~down:(nnf_rewriter srk) formula
      |> SrkSimplify.simplify_terms srk
    in
    let solver = Smt.mk_solver srk in
    Smt.Solver.add solver [formula];
    let rec go cubes =
      match Smt.Solver.get_model solver with
      | `Unsat -> cubes
      | `Unknown -> assert false
      | `Sat m ->
        match Interpretation.select_implicant m formula with
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

  let get_pre_cube_labels srk formula exists tr_symbols =
    let pre_symbols = pre_symbols tr_symbols in
    let post_symbols = post_symbols tr_symbols in
    let exists_pre x =
      exists x && not (Symbol.Set.mem x post_symbols)
    in
    let exists_post x =
      exists x && not (Symbol.Set.mem x pre_symbols)
    in
    let pre_labels = project_dnf srk exists_pre formula in
    let post_label =
      mk_and srk [formula;
                  mk_not srk (postify srk tr_symbols (mk_or srk pre_labels))]
      |> project_dnf srk exists_post
      |> mk_or srk
      |> preify srk tr_symbols
    in
    pre_labels, [post_label]


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
    let skolem_constants = Symbol.Set.filter (fun a -> not (exists a)) (symbols body) in
    let body = (rewrite srk ~down:(nnf_rewriter srk) body) in
    let body = Nonlinear.linearize srk body in
    let label = get_intersect_cube_labeling srk body exists tr_symbols in
    let graph = compute_edges srk tr_symbols label body in
    let num_sccs, func_sccs = BGraphComp.scc graph in
    let sccs = Array.make num_sccs  [] in
    BatArray.iteri (fun ind lab -> sccs.(func_sccs ind)<-(lab :: sccs.(func_sccs ind)))
      label;
    if num_sccs = 0 then
      {vasses= BatArray.init 0 (fun x -> assert false); formula=body; skolem_constants}
    else(
      let vassarrays = BatArray.map (fun scc -> compute_single_scc_vass ~exists srk tr_symbols scc body) sccs in
      let result = {vasses=vassarrays;formula=body; skolem_constants} in
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

  (*Set upper bounds on distance for each label from source. Can prob combine this function with ordering bounds*)
  let entrance_bounds srk entvars num_labels = 
    mk_and srk  (BatList.map 
                   (fun var -> mk_and srk 
                       [mk_leq srk (mk_zero srk) var;
                        mk_leq srk var (mk_real srk (QQ.of_int num_labels))]) 
                   entvars)

  (*Distance is 0 if and only if source label*)
  let entrance_source_cons srk entvars es =
    mk_and srk (BatList.mapi
                  (fun ind var ->
                     mk_iff 
                       srk 
                       (mk_eq srk (List.nth es ind) (mk_one srk))
                       (mk_eq srk var (mk_zero srk))) entvars)


  (*If not source label, and reached (dist < n), then there is flow on an edge originating from a node with dist this dist - 1*)
  let entrance_non_source_cons srk entvars transformermap nvarst in_sings =
    mk_and srk (BatList.mapi 
                  (fun ind var ->
                     mk_if 
                       srk 
                       (mk_and srk
                          [mk_lt srk (mk_zero srk) var;
                           mk_lt srk var (mk_real srk (QQ.of_int (List.length entvars)))])
                       (mk_or srk
                          (List.fold_left
                             (fun acc ele ->
                                let (pred, _, _) = List.nth transformermap ele in
                                (mk_and srk
                                   [mk_leq srk (mk_one srk) (List.nth nvarst ele);
                                    mk_eq srk (mk_sub srk (List.nth entvars pred) (mk_one srk)) var]) ::
                                acc
                             )
                             [mk_false srk]
                             in_sings.(ind))))
                  entvars)


  (*If no route from source to node with flow (dist = n), then no outgoing flow allowed*)
  let entrance_n srk entvars eset in_sings out_sings nvarst =
    mk_and srk 
      (BatList.mapi
         (fun ind var ->
            let (es,et) = List.nth eset ind in
            let in_sing_this = List.map (fun ind -> List.nth nvarst ind) in_sings.(ind) in
            let out_sing_this = List.map (fun ind -> List.nth nvarst ind) out_sings.(ind) in
            mk_if srk
              (mk_eq srk var (mk_real srk (QQ.of_int (List.length entvars))))
              (mk_and srk
                 (*Really only out_sing_this needed here. Other options will be 0; playing with them to see if any added efficiency boost*)
                 ((*[(mk_eq srk (mk_add srk (es :: et :: (in_sing_this @ out_sing_this))) (mk_zero srk))] ::*) 
                 (List.map (fun term -> mk_eq srk (mk_zero srk) term) (es :: et :: (in_sing_this @ out_sing_this))))))
         entvars)


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
    let label, graph, alphas, invars, invarmaxk = vass.label, vass.graph, vass.simulation, vass.invars, vass.invarmaxk in
    let simulation = alphas in

    let ests = create_es_et srk (Array.length label) in
    let in_out_one = exp_one_in_out_flow srk ests in
    let ests_one_or_zero = exp_each_ests_one_or_zero srk ests in
    let pre_post_conds = exp_pre_post_conds srk ests label tr_symbols in
    let pos_constraints_1 = create_exp_positive_reqs srk [fst (List.split ests); snd (List.split ests)] in

    (*If case is top localized to one scc; still require that a label is used*)
    if(M.nb_rows (unify (vass.simulation)) = 0) then
      ((mk_and srk [in_out_one; ests_one_or_zero; pre_post_conds(*; pos_constraints_1*)]), (fst (List.split ests)))
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
 
      let (form, (equiv_pairst, kvarst, ksumst)) =
        exp_base_helper srk tr_symbols loop_counter simulation transformers invars invarmaxk in
      let sum_n_eq_loop_counter = exp_nvars_eq_loop_counter srk nvarst loop_counter in
      let ks_less_than_ns = exp_kvarst_less_nvarst srk nvarst kvarst in
      let reachable_transitions = get_reachable_trans graph in
      let post_conds_const = exp_post_conds_on_transformers srk label 
          transformersmap reachable_transitions nvarst alphas tr_symbols in
      let in_sing, out_sing  = exp_compute_trans_in_out_index_numbers transformersmap (Array.length label) in
      let flow_consv_req = exp_consv_of_flow_new srk in_sing out_sing ests nvarst (-2) in
      let pos_constraints = create_exp_positive_reqs srk [nvarst] in
      let sx_constraints = exp_sx_constraints_flow srk equiv_pairst transformers (nvarst:: kvarst) 
          ((mk_add srk nvarst) :: ksumst) (unify alphas) tr_symbols in_sing out_sing
          ests in
      let ent_bounds = entrance_bounds srk entvars (Array.length label) in
      let ent_source = entrance_source_cons srk entvars (fst (List.split ests)) in
      let ent_non_source = entrance_non_source_cons srk entvars transformersmap nvarst in_sing in
      let ent_max = entrance_n srk entvars ests in_sing out_sing nvarst in 
      let form = mk_and srk [form; sum_n_eq_loop_counter; ks_less_than_ns; flow_consv_req; in_out_one;
                             ests_one_or_zero; pre_post_conds; pos_constraints; pos_constraints_1; post_conds_const; sx_constraints;
                             ent_bounds; ent_source; ent_non_source; ent_max] in
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

  (*If last scc used, link x' vars to this scc*)
  let used_last_scc srk orderings_vars num_scc_used symmappings syms =
    mk_and srk (BatArray.to_list (BatArray.mapi (fun ind1 o_var1 ->
        mk_if srk (mk_eq srk o_var1 num_scc_used)
          (mk_and srk (BatList.map2 (fun (x, x') (sccx, sccx') -> mk_eq srk (mk_const srk x') (mk_const srk sccx'))
                         syms symmappings.(ind1)))) orderings_vars))

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
      let subloop_counters = BatArray.mapi (fun ind1 scc ->
          mk_const srk ((mk_symbol srk ~name:("counter_"^(string_of_int ind1)) `TyInt))) sccsform.vasses in
      let symmappings = BatArray.mapi (fun ind1 scc ->
          List.rev
            (BatList.fold_lefti (fun acc ind2 (x, x') ->
                 ((mk_symbol srk ~name:((show_symbol srk x)^"_"^(string_of_int ind1)) (typ_symbol srk x)),
                  (mk_symbol srk ~name:((show_symbol srk x')^"_"^(string_of_int ind1)) (typ_symbol srk x'))) :: acc) [] syms))
          sccsform.vasses
      in
      let skolem_mappings = BatArray.mapi (fun ind1 scc ->
          BatList.fold_left 
            (fun acc x -> (x, (mk_symbol srk ~name:((show_symbol srk x)^"_"^(string_of_int ind1)) (typ_symbol srk x))) 
                          :: acc)
            []
            (Symbol.Set.elements sccsform.skolem_constants))
          sccsform.vasses
      in
      let skolem_mappings_transitions = BatArray.mapi (fun ind1 scc ->
          BatList.fold_left 
            (fun acc x -> (x, (mk_symbol srk ~name:((show_symbol srk x)^"_"^(string_of_int ind1)) (typ_symbol srk x))) 
                          :: acc)
            []
            (Symbol.Set.elements sccsform.skolem_constants))
          sccsform.vasses
      in

      let sccclosures_es = BatArray.mapi (fun ind vass -> closure_of_an_scc srk syms subloop_counters.(ind) vass) sccsform.vasses in
      let sccclosures, es = BatList.split (BatArray.to_list sccclosures_es) in
      let sccclosures, es = BatArray.of_list sccclosures, BatArray.of_list es in
      (*We compute scc closure without scc specific x, x' and then add these in after closure*)
      let sccclosures = BatArray.mapi (fun ind closure ->  
          (postify srk skolem_mappings.(ind) 
             (postify srk (merge_mappings syms symmappings.(ind) false true) 
                (postify srk (merge_mappings syms symmappings.(ind) true false) closure))))
          sccclosures in

      let scclabels = BatArray.map (fun scc -> mk_or srk (BatArray.to_list scc.label)) sccsform.vasses in		
      let sccgraph = compute_edges srk syms scclabels sccsform.formula in
      let num_scc_used = mk_const srk (mk_symbol srk ~name:("Num_scc_used") `TyInt) in
      let order = List.rev (BGraphTopo.fold (fun v acc -> Log.errorf "THIS SCC REACHED %d" v; v :: acc) sccgraph []) in
      let sub_loops_geq_0 = create_exp_positive_reqs srk [Array.to_list subloop_counters] in
      let scc_ordering = BatArray.mapi (fun ind1 scc ->
          mk_const srk ((mk_symbol srk ~name:("ordering_"^(string_of_int ind1)) `TyInt))) sccsform.vasses in
      let order_bounds_const = ordering_bounds srk scc_ordering (mk_real srk (QQ.of_int (BatArray.length sccclosures))) in
      let no_dups_constr = no_dups_ordering srk scc_ordering in
      let come_next_const = come_next_req srk scc_ordering es subloop_counters num_scc_used sccclosures symmappings syms sccsform.formula skolem_mappings_transitions in
      let first_scc_const = first_scc_used srk scc_ordering es sccclosures symmappings syms in
      let last_scc_const = used_last_scc srk scc_ordering num_scc_used symmappings syms in
      let num_scc_used_bound = mk_and srk 
          [mk_lt srk num_scc_used (mk_real srk (QQ.of_int (BatArray.length sccclosures)));
           mk_leq srk (mk_zero srk) num_scc_used] in
      let loop_bound = mk_eq srk (mk_add srk (num_scc_used :: (BatArray.to_list subloop_counters))) loop_counter in
      let order_constr = topo_order_constraints srk order es scc_ordering in
      let result = mk_or srk [mk_and srk [order_bounds_const; sub_loops_geq_0; no_dups_constr; come_next_const; first_scc_const;
                                          last_scc_const; num_scc_used_bound; loop_bound; mk_leq srk (mk_zero srk) loop_counter; order_constr];
                              no_trans_taken srk loop_counter syms] in
      Log.errorf "Done";
      result
    )



  let join _ _ _ _ = assert false
  let widen _ _ _ _ = assert false
  let equal _ _ _ _ = assert false


end

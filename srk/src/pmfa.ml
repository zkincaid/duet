open Syntax



let typ_symbol_fo srk sym =
    match typ_symbol srk sym with
    | `TyInt -> `TyInt
    | `TyReal -> `TyReal
    | `TyBool -> `TyBool
    | `TyArr -> `TyArr
    | _ -> assert false


(* Replaces existentially bound vars with skolem constants. *)
let skolemize srk phi =
  let decapture_tbl = BatHashtbl.create 97 in
  let subst = 
    Memo.memo (fun (ind, typ) ->
        let sym = mk_symbol srk (typ :> typ) in
        BatHashtbl.add decapture_tbl sym ind;
        mk_const srk sym)
  in
  let phi = 
    substitute
      srk
      subst phi
  in
  let rec subst_existentials subst_lst expr =
    match Formula.destruct srk expr with
    | `Quantify (`Exists, name, typ, phi) ->
      subst_existentials ((mk_symbol srk ~name (typ :> typ)) :: subst_lst) phi
    | `And conjuncts ->
      mk_and srk (List.map (subst_existentials subst_lst) conjuncts)
    | `Or disjuncts ->
      mk_or srk (List.map (subst_existentials subst_lst) disjuncts)
    | open_form ->
      (* TODO: make substitute more efficient *)
      substitute
        srk
        (fun (i, _) -> 
             mk_const srk (List.nth subst_lst i))
        (Formula.construct srk open_form)
  in
  substitute_sym
    srk
    (fun sym ->
       if Hashtbl.mem decapture_tbl sym then
         mk_var srk (Hashtbl.find decapture_tbl sym) (typ_symbol_fo srk sym)
       else mk_const srk sym)
    (subst_existentials [] phi)



module OldPmfa = struct
  open Syntax
  open Iteration
  module V = Linear.QQVector
  module M = Linear.QQMatrix
  module Z = Linear.ZZVector
  module H = Abstract
  module T = TransitionFormula
  include Log.Make(struct let name = "srk.array:" end)

  let arr_trs srk tf = 
    List.filter (fun (s, _) -> typ_symbol srk s = `TyArr) (T.symbols tf)

  let int_trs srk tf =
    List.filter (fun (s, _) -> (typ_symbol srk s = `TyInt)) (T.symbols tf)

  let flatten syms = List.fold_left (fun acc (sym, sym') -> sym :: sym' :: acc) [] syms 
  
  (* Projects an array transition formula [tf] down to a single symbolic index
   * [j]. The dynamics of element [j] of array transition variables (a, a') 
   * are captured with the integer transition variables ([map] a, [map] a'). *)
  let projection srk tf =
    let map = Hashtbl.create (List.length (arr_trs srk tf) * 8 / 3) in
    let j = mk_symbol srk ~name:"j" `TyInt in
    let j' = mk_symbol srk ~name:"j'" `TyInt in

    let f (trs, phi) (a, a') = 
      let z = mk_symbol srk ~name:("z"^(show_symbol srk a)) `TyInt in
      let z' = mk_symbol srk ~name:("z'"^(show_symbol srk a')) `TyInt in
      Hashtbl.add map z a;
      Hashtbl.add map z' a';
      (z, z') :: trs,
      mk_and 
        srk 
        [mk_eq srk (mk_const srk z) (mk_select srk (mk_const srk a) (mk_const srk j));
         mk_eq srk (mk_const srk z') (mk_select srk (mk_const srk a') (mk_const srk j));
         phi]
    in
    let integer_trs, phi = 
      List.fold_left f ((j, j') :: int_trs srk tf, T.formula tf) (arr_trs srk tf) 
    in
    (* TODO: Fix assumption that no symbolic constants *)
    let phi = 
      mk_exists_consts srk (fun sym -> List.mem sym (flatten integer_trs)) phi 
    in
    j, j', map, T.make (mk_and srk [phi; mk_eq srk (mk_const srk j) (mk_const srk j')]) integer_trs 

  (* Convert from a pmfa formula to an mfa formula.
   * We achieve this by converting the pmfa formula to an equivalent formula
   * in qnf such that there is a single universal quantifier. The key algorithm
   * thus is just a merging of the matrices under potentially many (non-nested) 
   * universal quantifiers. We factor the universal quantifier over disjunction
   * by introducing a new quantified integer sorted variable that acts a boolean
   * that determines which disjunct is "on".*)
  let to_mfa srk tf =
    (* We first subsitute in for each existentially quantified variable
     * a new variable symbol. This results in each universal quantifier 
     * having debruijn index 0 and makes the merging function that follows
     * easier. We undo this substitution prior to the end of this [pmfa_to_lia].*)
    let new_vars = ref (Symbol.Set.empty) in 
    let rec subst_existentials subst_lst expr =
      match Formula.destruct srk expr with
      | `Quantify (`Exists, name, typ, phi) ->
        let new_subst_var = mk_symbol srk ~name (typ :> typ) in
        new_vars := Symbol.Set.add new_subst_var (!new_vars);
        subst_existentials ((mk_const srk new_subst_var) :: subst_lst) phi
      | `And conjuncts -> 
        mk_and srk (List.map (subst_existentials subst_lst) conjuncts)
      | `Or disjuncts ->
        mk_or srk (List.map (subst_existentials subst_lst) disjuncts)
      | open_form ->
        substitute
          srk
          (fun (i, _) -> List.nth subst_lst i)
          (Formula.construct srk open_form)
    in
    let phi = subst_existentials [] (T.formula tf) in
    let rec merge_univ merge_eqs expr =
      match Formula.destruct srk expr with
      | `Quantify (`Forall, _, `TyInt, phi) -> mk_and srk (phi :: merge_eqs)
      | `And conjs -> mk_and srk (List.map (merge_univ merge_eqs) conjs)
      | `Or disjs ->
        let sym = mk_symbol srk ~name:"casesplit" `TyInt in
        new_vars := Symbol.Set.add sym (!new_vars); 
        let s = mk_const srk sym in
        let append_ind_eqlty ind = mk_eq srk (mk_int srk ind) s ::  merge_eqs in
        mk_or srk (List.mapi (fun ind -> merge_univ (append_ind_eqlty ind)) disjs)
      | open_form -> Formula.construct srk open_form
    in
    let body = merge_univ [] phi in
    (* Note that we haven't actually associated free var 0 of body with a 
     * universal quantifier yet. We do this at the end of [mfa_to_lia]*)
    body, !new_vars


  let mfa_to_lia srk body =
    (* We replace the univ. quant variable with a symbol to simplify the rest
     * of [mfa_to_lia].*)
    let uq_sym = mk_symbol srk `TyInt in
    let uq_term = mk_const srk uq_sym in
    let body = 
      substitute srk (fun (i, _) -> if i = 0 then uq_term else assert false) body 
    in
    (* [uqr_syms] is the set of symbols that will be existentially quantified
     * in front of the universal quantifier *)
    let uqr_syms = ref Symbol.Set.empty in
    let get_arr a =
      match ArrTerm.destruct srk a with
      | `App (a, _) -> a
      | _ -> assert false
    in
    (* Maps the term a[i] to an integer symbol where i is the universally
     * quantified var *)
    let uq_read =
      Memo.memo (fun a -> 
          let sym = mk_symbol srk ~name:(show_symbol srk (get_arr a)) `TyInt in
          uqr_syms := Symbol.Set.add sym !uqr_syms;
          sym)
    in
    (* [nuqr_syms] is the set of symbols that will be existentially quantified
     * at the head of the lia formula *)
    let nuqr_syms = ref Symbol.Set.empty in
    let func_consist_reqs : ('a arr_term, 'a arith_term) Hashtbl.t = Hashtbl.create 100 in
    (* Maps the term a[i] to an integer symbol where i is not the universally
     * quantified var *)
    let non_uq_read : 'c * 'd -> 'a arith_term =
      Memo.memo (fun (arr, read) -> 
          Hashtbl.add func_consist_reqs arr read;
          let sym = mk_symbol srk `TyInt in
          nuqr_syms := Symbol.Set.add sym !nuqr_syms;
          mk_const srk sym)
    in
    (* TODO: Make sure that array reads normalized for efficiency; don't want
     * seperate symbol for a[x + y] vs a[y + x]*)
    let rec termalg = function
      |  `Select (a, i) -> 
        if ArithTerm.equal i uq_term 
        then (mk_const srk (uq_read a))
        else (non_uq_read (a, i) :> ('a, typ_arith) expr)
      | `Ite (cond, bthen, belse) ->
        mk_ite srk (Formula.eval srk formalg cond) bthen belse
      | open_term -> ArithTerm.construct srk open_term 
    and formalg = function
      | `Atom (`Arith (`Eq, x, y)) -> 
        let lhs = (ArithTerm.eval srk termalg x) in
        let rhs = (ArithTerm.eval srk termalg y) in
        mk_eq srk  lhs rhs   
      | `Atom (`Arith (`Leq, x, y)) ->
        mk_leq srk (ArithTerm.eval srk termalg x) (ArithTerm.eval srk termalg y)
      | `Atom (`Arith(`Lt, x, y)) -> 
        mk_lt srk (ArithTerm.eval srk termalg x) (ArithTerm.eval srk termalg y)
      | open_formula -> Formula.construct srk open_formula
    in
    let reads_replaced = Formula.eval srk formalg body in
    let functional_consistency_clauses =
      List.map (fun (arr, read) ->
          mk_if 
            srk 
            (mk_eq srk uq_term read)
            (mk_eq srk (mk_const srk (uq_read arr)) (non_uq_read (arr, read))))
        (BatHashtbl.to_list func_consist_reqs)
    in
    let matrix = mk_and srk (reads_replaced :: functional_consistency_clauses) in
    let phi' = 
      mk_exists_consts srk (fun sym -> not (Symbol.Set.mem sym !uqr_syms)) matrix 
    in
    let phi' = mk_forall_const srk uq_sym phi' in
    mk_exists_consts srk (fun sym -> not (Symbol.Set.mem sym !nuqr_syms)) phi'


  let pmfa_to_lia srk tf =
    let tf = TransitionFormula.map_formula (eliminate_ite srk) tf in
    let mfa, new_vars = to_mfa srk tf in
    let lia = mfa_to_lia srk mfa in
    let phi = 
      mk_exists_consts srk (fun sym -> (not (Symbol.Set.mem sym new_vars))) lia
    in
    T.make ~exists:(T.exists tf) phi (T.symbols tf)

  
 let eliminate_stores srk phi =
  let mk_op op =
    match op with
    | `Eq -> mk_eq
    | `Lt -> mk_lt
    | `Leq -> mk_leq
  in
  let rec rewrite_store index node =
    match ArrTerm.destruct srk node with
    | `Store (a, i, v) ->
      let i = ArithTerm.eval srk arith_alg i in
      let v = ArithTerm.eval srk arith_alg v in
      mk_ite srk (mk_eq srk i index) v (rewrite_store index a)
    | `Var (ind, `TyArr) -> mk_select srk (mk_var srk ind `TyArr) index
    | `App (a, []) -> mk_select srk (mk_const srk a) index
    | `Ite (phi, a, b) -> 
      mk_ite 
        srk 
        (Formula.eval srk alg phi) 
        (rewrite_store index a)
        (rewrite_store index b)
    | _ -> assert false
  and  arith_alg = function
    | `Select (a, i) -> rewrite_store i a
    | `Ite (phi, x, y) -> mk_ite srk (Formula.eval srk alg phi) x y
    | open_term -> ArithTerm.construct srk open_term
  and alg = function
    | `Atom (`Arith (op, x, y)) ->
      (mk_op op) srk (ArithTerm.eval srk arith_alg x) (ArithTerm.eval srk arith_alg y)
    | `Atom(`ArrEq (a, b)) -> 
      let index = mk_symbol srk `TyInt in
      let lhs = rewrite_store (mk_const srk index) a in
      let rhs = rewrite_store (mk_const srk index) b in
      mk_forall_const srk index (mk_eq srk lhs rhs)
    | open_formula -> Formula.construct srk open_formula
  in
  Formula.eval srk alg phi

 (* Changes bool syms to int syms... when I wrote this some of the other functions
  * in this module failed with presence of booleans. Need to check if this is still the
  * case if not just fix this. This function messes with types of tr_symbols are that
  * worries me*)
 let unbooleanize srk phi =
      let phi = skolemize srk phi in 
      let symbols = symbols phi in
      let map = Hashtbl.create 97 in
      Symbol.Set.iter (fun ele ->
          let int_sym = mk_symbol srk ~name:(show_symbol srk ele) `TyInt in
          Hashtbl.add map ele int_sym)
        (Symbol.Set.filter (fun ele -> typ_symbol srk ele = `TyBool) symbols);
      let phi_subst = 
        substitute_const 
          srk
          (fun s -> 
             if BatHashtbl.mem map s then
               mk_eq srk (mk_one srk) (mk_const srk (BatHashtbl.find map s))
             else
               mk_const srk s)
          phi
      in
      let bool_constrs =
        BatHashtbl.fold (fun _ sym acc -> 
            mk_or 
              srk 
              [mk_eq srk (mk_const srk sym) (mk_one srk);
               mk_eq srk (mk_const srk sym) (mk_zero srk)] :: acc)
          map
          []
      in
      mk_and srk (phi_subst :: bool_constrs) 



  module Array_analysis (Iter : PreDomain) = struct

    type 'a t = 
      { iter_obj : 'a Iter.t; 
        proj_ind : Symbol.t;
        proj_indpost : Symbol.t;
        arr_map : (Symbol.t, Symbol.t) Hashtbl.t;
        iter_trs : (Symbol.t * Symbol.t) list;
        ground_lia : 'a formula}

    let abstract srk tf =
      let exists = TransitionFormula.exists tf in
      let phi = eliminate_stores srk (T.formula tf) in
      let phi = eliminate_ite srk phi in
      let phi = unbooleanize srk phi in
      let tf_pmfa = T.map_formula (fun _ -> phi) tf in
      let proj_ind, proj_indpost, arr_map, tf_proj = projection srk tf_pmfa in
      let lia_tf = pmfa_to_lia srk tf_proj in
      (* Didn't include quant functions in this pr *)
      let lia = Quantifier.eg_simplification srk (T.formula lia_tf) in
      let ground_lia = Quantifier.mbp_qe_inplace srk lia in
      let ground_tf = TransitionFormula.make ~exists ground_lia (T.symbols lia_tf) in
      let iter_obj = Iter.abstract srk ground_tf in

      {iter_obj;
       proj_ind;
       proj_indpost;
       arr_map;
       iter_trs=(T.symbols lia_tf);
       ground_lia;}

    type 'a dir_var = Inc of 'a arith_term * 'a arith_term | Dec of 'a arith_term * 'a arith_term
    
    (* Determines which trs in phi are monotonically increasing/decreasing *)
    let directional_vars srk phi trs =
      List.flatten (
        List.filter_map (fun (x, x') ->
            let xt, xt' = mk_const srk x, mk_const srk x' in
            match Smt.entails srk phi (mk_leq srk xt xt'), 
                  Smt.entails srk phi (mk_leq srk xt' xt) with
            | `Yes, `Yes -> Some [Inc (xt, xt'); Dec (xt, xt')]
            | `Yes, _ -> Some [Inc (xt, xt')]
            | _, `Yes -> Some [Dec (xt, xt')]
            | _ -> None)
          trs)

    let create_phased_exps srk phi trs symb_index directs lc =
      let exp1term = mk_symbol srk ~name:"exp1" `TyInt in
      let exp2term = mk_symbol srk ~name:"exp2" `TyInt in
      List.map (fun direction ->
          match direction with
          | Inc (x, x') ->
            let j = mk_const srk symb_index in

            let phase1 = 
              T.make 
                (mk_and srk 
                   [Iter.exp
                      srk 
                      trs 
                      (mk_const 
                         srk 
                         exp1term) 
                         (Iter.abstract 
                            srk 
                            (T.make (mk_and srk [phi; mk_leq srk x j; mk_leq srk x' j]) trs));
                    mk_leq srk x j; mk_leq srk x' j])
                trs
            in
            let phase2 =
              T.make
                (mk_and srk 
                   [Iter.exp
                      srk 
                      trs 
                      (mk_const 
                         srk 
                         exp2term)
                         (Iter.abstract 
                            srk 
                            (T.make (mk_and srk [phi; mk_lt srk j x; mk_lt srk j x']) trs));
                    mk_lt srk j x; mk_lt srk j x'])
                trs
            in
            let intermediate_tr = 
              T.make 
                (mk_and srk [phi; mk_leq srk x j; mk_lt srk j x'])
                trs
            in

            let phased_tr = T.mul srk (T.mul srk phase1 intermediate_tr) phase2 in

            (* Adds constraints on loop counter depending on which phase(s) taken*)
            let both_phases = 
              T.map_formula (fun f ->
                  mk_and 
                    srk
                    [mk_eq 
                       srk 
                       lc 
                       (mk_add srk [mk_const srk exp2term;
                                    mk_const srk exp1term;
                                    mk_int srk 1]);
                     f])
                phased_tr
            in
            let phase1_only = 
              T.map_formula (fun f ->
                  mk_and 
                    srk
                    [mk_eq srk lc (mk_const srk exp1term);
                     f])
                phase1
            in
            let phase2_only = 
              T.map_formula (fun f ->
                  mk_and 
                    srk
                    [mk_eq srk lc (mk_const srk exp2term);
                     f])
                phase2
            in
                     

            let phased_exp =
              T.map_formula
                (fun f ->
                   mk_and
                     srk
                     [mk_leq srk (mk_zero srk) (mk_const srk exp1term); 
                      mk_leq srk (mk_zero srk) (mk_const srk exp2term);
                      f]) 
                (T.add srk (T.add srk both_phases phase1_only) phase2_only)
            in
            (* Need to quantify over newly introduce symbols *)
            (*
            let final =
              mk_exists_consts
                srk
                (fun sym -> not (Symbol.Set.mem sym !exists))
                entire_formula
            in*)
            T.map_formula 
              (fun f ->
                 mk_exists_const srk exp1term (mk_exists_const srk exp2term f))
              phased_exp

          | Dec _ -> T.make (mk_true srk) trs (* turned off for now to make testing smoother *)
            )
        directs, exp1term, exp2term

    
    
    
    let exp srk _ lc obj =
      let directs = directional_vars srk obj.ground_lia obj.iter_trs in
      let directs_res, _, _ = create_phased_exps srk obj.ground_lia obj.iter_trs obj.proj_ind directs lc in
      let noop_eqs = 
        List.map 
          (fun (x, x') -> mk_eq srk (mk_const srk x) (mk_const srk x'))
          obj.iter_trs
      in
      (* Redo this part to act on tfs rather than first converting to formula *)
      let directs_res = List.map (fun f -> T.formula f) directs_res in
      let direct_res = mk_and srk directs_res in
      let direct_res = Quantifier.mbp_qe_inplace srk direct_res in 
      let exp_res_pre = 
        mk_or 
          srk 
          [mk_and srk ((mk_eq srk lc (mk_int srk 0)) :: noop_eqs); direct_res] 
      in
      let map sym =  
        if sym = obj.proj_ind || sym = obj.proj_indpost 
        then mk_var srk 0 `TyInt
        else if Hashtbl.mem obj.arr_map sym 
        then mk_select srk (mk_const srk (Hashtbl.find obj.arr_map sym)) 
            (mk_var srk 0 `TyInt) 
        else mk_const srk sym
      in
      let substed = substitute_const srk map exp_res_pre in
      let res = (mk_forall srk `TyInt substed) in
      res

    let pp _ _ _= failwith "todo 10"

  end
end

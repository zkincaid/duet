open Syntax
open BatPervasives
open Iteration
module V = Linear.QQVector
module M = Linear.QQMatrix
module Z = Linear.ZZVector
module H = Abstract
module T = TransitionFormula
include Log.Make(struct let name = "srk.array:" end)

let time s =
    let t = Unix.gettimeofday () in
    Log.errorf "\n%s Curr time: %fs\n" s (t); t

let diff t1 t2 s =
    Log.errorf "\n%s Execution time: %fs\n" s (t2 -. t1)

let arr_trs srk tf = 
  List.filter (fun (s, _) -> typ_symbol srk s = `TyArr) (T.symbols tf)

let int_trs srk tf =
  List.filter (fun (s, _) -> (typ_symbol srk s = `TyInt)) (T.symbols tf)

let flatten syms = List.fold_left (fun acc (sym, sym') -> sym :: sym' :: acc) [] syms 

(** Subsitute tbl[sym] for sym in phi for any sym that appears in tbl *)
let tbl_subst srk phi tbl = 
  substitute_const 
    srk 
    (fun sym -> BatHashtbl.find_default tbl sym (mk_const srk sym))
    phi

(* Projects an array transition formula [tf] down to a single symbolic index
 * [j]. The dynamics of element [j]  of array transition variables (a, a') 
 * are captured with the integer transition variables ([map] a, [map] a'). *)
let projection srk tf =
  let map = Hashtbl.create (List.length (arr_trs srk tf) * 8 / 3) in
  let j = mk_symbol srk ~name:"j" `TyInt in
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
    List.fold_left f ((j, j) :: int_trs srk tf, T.formula tf) (arr_trs srk tf) 
  in
  (* TODO: This quantifies symbolic constants - is that an issue? *)
  let phi = 
    mk_exists_consts srk (fun sym -> List.mem sym (flatten integer_trs)) phi 
  in
  j, map, T.make phi integer_trs 

(* Convert from a pmfa formula to an mfa formula.
 * We achieve this by converting the pmfa formula to an equivalent formula
 * in qnf such that there is a single universal quantifier. The key algorithm
 * thus is just a merging of the matrices under potentially many (non-nested) 
 * universal quantifiers. We factor the universal quantifier over disjunction
 * by introducing a new quantified integer sorted variable that acts a boolean
 * and determines which disjunct is "on".*)
let to_mfa srk tf =
  (* We first subsitute in for each existentially quantified variable
   * a new variable symbol. This allows us to focus solely on the universal
   * quantifiers during the merging function that follows. We undo this
   * substitution prior to the end of this function.*)
  (* TODO: Quantifier elim via equality checking becomes much more difficult 
   * after this step. Make sure a go at it happens prior to this step *)
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
      (* TODO: make substitute more efficient *)
      substitute
        srk
        (fun i -> List.nth subst_lst i)
        (Formula.construct srk open_form)
  in
  let phi = subst_existentials [] (T.formula tf) in
  (*TODO: If we convert to DNF first, we can likely limit ourselves to introducing
   * only a single new quantifier. This should have payoffs when in comes to
   * eliminating the quantifiers later on *)
  let rec merge_univ merge_eqs expr =
    match Formula.destruct srk expr with
    | `Quantify (`Forall, _, `TyInt, phi) -> mk_and srk (phi :: merge_eqs)
    | `And conjs -> mk_and srk (List.map (merge_univ merge_eqs) conjs)
    | `Or disjs ->
      let sym = mk_symbol srk `TyInt in
      new_vars := Symbol.Set.add sym (!new_vars); 
      let s = mk_const srk sym in
      let append_ind_eqlty ind = mk_eq srk (mk_int srk ind) s ::  merge_eqs in
      mk_or srk (List.mapi (fun ind -> merge_univ (append_ind_eqlty ind)) disjs)
    | open_form -> Formula.construct srk open_form
  in
  let body = merge_univ [] phi in
  mk_forall srk `TyInt body, !new_vars
 

let mfa_to_lia srk phi =
  let body = 
    match destruct srk phi with
    | `Quantify (`Forall, _, `TyInt, body) -> body
    | _ -> failwith "mfa formula needs to start with leading univ quant"
  in
  (* We are going to introduce a bunch of new quantifiers later on. We set
   * the univ quant var to a symbol to cut down on number of substs performed*)
  let uq_sym = mk_symbol srk `TyInt in
  let uq_term = mk_const srk uq_sym in
  let body = 
    substitute srk (fun i -> if i = 0 then uq_term else assert false) body 
  in
  let uqr_syms = ref Symbol.Set.empty in
  (* Maps the term a[i] to an integer symbol where i is the universally
   * quantified var *)
  let uq_read =
    Memo.memo (fun _ -> 
        let sym = mk_symbol srk ~name:"SYMREAD"`TyInt in
        uqr_syms := Symbol.Set.add sym !uqr_syms;
        sym)
  in
  let nuqr_syms = ref Symbol.Set.empty in
  let func_consist_reqs : ('a term, 'a term) Hashtbl.t = Hashtbl.create 100 in
  (* Maps the term a[i] to an integer symbol where i is not the universally
   * quantified var *)
  let non_uq_read : 'c * 'd -> 'a term =
    Memo.memo (fun (arr, read) -> 
        Hashtbl.add func_consist_reqs arr read;
        let sym = mk_symbol srk `TyInt in
        nuqr_syms := Symbol.Set.add sym !nuqr_syms;
        mk_const srk sym)
  in
  (* TODO: Make sure that array reads normalized for efficiency *)
  let rec termalg = function
    | `Binop(`Select, a, i) -> 
      if Term.equal i uq_term 
      then (mk_const srk (uq_read a))
      else (non_uq_read (a, i) :> ('a, typ_term) expr)
    | `Ite (cond, bthen, belse) ->
      mk_ite srk (Formula.eval srk formalg cond) bthen belse
    | open_term -> Term.construct srk open_term 
  and formalg = function
    | `Atom (`Eq, x, y) -> 
      let lhs = (Term.eval srk termalg x) in
      let rhs = (Term.eval srk termalg y) in
      mk_eq srk  lhs rhs   
    | `Atom (`Leq, x, y) ->
      mk_leq srk (Term.eval srk termalg x) (Term.eval srk termalg y)
    | `Atom (`Lt, x, y) -> 
      mk_lt srk (Term.eval srk termalg x) (Term.eval srk termalg y)
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
  let mfa, new_vars = to_mfa srk tf in
  let lia = mfa_to_lia srk mfa in
  let phi = 
    mk_exists_consts srk (fun sym -> (not (Symbol.Set.mem sym new_vars))) lia
  in
  T.make ~exists:(T.exists tf) phi (T.symbols tf)



let eliminate_stores srk phi =
  let rec rewrite_store index node =
    match Term.destruct srk node with
    | `Store (a, i, v) ->
        let i = Term.eval srk term_alg i in
        let v = Term.eval srk term_alg v in
        mk_ite srk (mk_eq srk i index) v (rewrite_store index a)
    | `Var (ind, `TyArr) -> mk_select srk (mk_var srk ind `TyArr) index
    | `App (a, []) -> mk_select srk (mk_const srk a) index
    | _ -> assert false (*invalid_arg "ill-formed array store"*)
  and  term_alg = function 
    | `Binop(`Select, a, i) -> rewrite_store i a
    | open_term -> Term.construct srk open_term
        in
  let alg = function
    | `Atom (`Eq, x, y) ->
        begin match expr_typ srk x with
        | `TyArr ->
            let index = mk_symbol srk `TyInt in
            let lhs = rewrite_store (mk_const srk index) x in
            let rhs = rewrite_store (mk_const srk index) y in
            mk_forall_const srk index (mk_eq srk lhs rhs)
        | _ -> mk_eq srk (Term.eval srk term_alg x) (Term.eval srk term_alg y)
      end
        | `Atom (`Lt, x, y) -> 
            mk_lt srk (Term.eval srk term_alg x) (Term.eval srk term_alg y)
        | `Atom (`Leq, x, y) ->
            mk_leq srk (Term.eval srk term_alg x) (Term.eval srk term_alg y)
        | open_formula -> Formula.construct srk open_formula
            in
  Formula.eval srk alg phi




module Array_analysis (Iter : PreDomain) = struct

  type 'a t = 
    { iter_obj : 'a Iter.t; 
      proj_ind : Symbol.t; 
      arr_map : (Symbol.t, Symbol.t) Hashtbl.t;
      new_trs : (Symbol.t * Symbol.t) list;
      iter_trs : (Symbol.t * Symbol.t) list;
      projed_form : 'a formula;
      flag : bool}
  
  (* TODO:Clean up and actually use tf*)
  let abstract srk tf =
    let t1 = time "In abstract" in
    let exists = TransitionFormula.exists tf in
    let tr_symbols = TransitionFormula.symbols tf in
    let flag = ref false in
    let tr_symbols = match typ_symbol srk (fst (List.hd tr_symbols)) with
      | `TyBool -> flag := true; List.tl tr_symbols
      | _ -> tr_symbols 
    in
    let tf = T.make ~exists:(T.exists tf) (eliminate_stores srk (T.formula tf)) tr_symbols in
    let proj_ind, arr_map, tf_proj = projection srk tf in
    let lia = pmfa_to_lia srk tf_proj in
    let phi = Quantifier.miniscope srk (T.formula lia) in
    let phi = Quantifier.eq_guided_qe srk phi in
    to_file srk phi "/Users/jakesilverman/Documents/duet/duet/REWRITE.smt2";
    let new_trs = List.filter (fun a -> not (List.mem a tr_symbols)) (T.symbols lia) in
    let ground  = Quantifier.mbp_qe_inplace srk phi in
    let ground_tf = TransitionFormula.make ~exists ground (T.symbols lia) in
    let iter_obj = Iter.abstract srk ground_tf in
    to_file srk ground "/Users/jakesilverman/Documents/duet/duet/GROUND2.smt2";
    let t2 = time "EXIT abstract" in
    diff t1 t2 "ABSTRACT";
    {iter_obj;
     proj_ind;
     arr_map;
     new_trs;
     iter_trs=(T.symbols lia);
     projed_form=ground;
     flag=(!flag)}


  (*let equal _ _ _ _= failwith "todo 5"

  let widen _ _ _ _= failwith "todo 6"

  let join _ _ _ _ = failwith "todo 7"
*)
  let split_append lst = 
    let a, b = List.split lst in
    a @ b

  let special_step srk fo_trs proj_phi proj_phi_exp temp_lc_sym lc arr_projs proj_ind =
    let step_focus = mk_symbol srk ~name:"s" `TyInt in
    let step_noop = mk_symbol srk ~name:"p" `TyInt in
    let pre_tbl = Hashtbl.create (List.length fo_trs) in
    let post_tbl = Hashtbl.create (List.length fo_trs) in
    let intermediate_tbl = Hashtbl.create (2*(List.length fo_trs)) in
    let inter_syms = ref [] in
    List.iter
      (fun (sym, sym') ->
         if sym = proj_ind then (
           Hashtbl.add pre_tbl sym (mk_const srk sym);
           Hashtbl.add intermediate_tbl sym (mk_const srk sym);
           Hashtbl.add intermediate_tbl sym (mk_const srk sym);
           Hashtbl.add post_tbl sym (mk_const srk sym))
         else (

         let fresh_copy sym = mk_symbol srk ~name:((show_symbol srk sym)^"''") `TyInt in
         let sym'' = fresh_copy sym in
         let sym''' = fresh_copy sym' in
         inter_syms := sym'' :: sym''' :: !inter_syms;
         Hashtbl.add pre_tbl sym' (mk_const srk sym'');
         Hashtbl.add intermediate_tbl sym (mk_const srk sym'');
         Hashtbl.add intermediate_tbl sym' (mk_const srk sym''');
         Hashtbl.add post_tbl sym (mk_const srk sym''')))
      fo_trs;
    let inter_syms = !inter_syms in
    let equalities = 
      List.fold_left 
        (fun eqs (x, x') -> 
           mk_eq srk (mk_const srk x) (Hashtbl.find intermediate_tbl x) ::
           mk_eq srk (mk_const srk x') (Hashtbl.find intermediate_tbl x') ::
           eqs)
        []
        arr_projs
    in
    let neutralize_step_at step =
      Hashtbl.add 
        post_tbl 
        temp_lc_sym 
        (mk_sub srk lc (mk_add srk [mk_int srk 1; mk_const srk step]));
      Hashtbl.add pre_tbl temp_lc_sym (mk_const srk step);
      let res = 
        mk_and
          srk
          [tbl_subst srk proj_phi_exp pre_tbl;
           tbl_subst srk proj_phi intermediate_tbl;
           tbl_subst srk proj_phi_exp post_tbl]
      in
      Hashtbl.remove post_tbl temp_lc_sym;
      Hashtbl.remove pre_tbl temp_lc_sym;
      res
    in
    mk_forall_const
      srk 
      step_focus
      (mk_if
         srk
         (mk_and
            srk
            [mk_leq srk (mk_int srk 0) (mk_const srk step_focus);
             mk_lt srk (mk_const srk step_focus) lc;
             mk_forall_consts
               srk
               (fun sym -> not (List.mem sym (step_noop :: inter_syms)))
               (mk_if
                  srk
                  (mk_and
                     srk
                     [mk_leq srk (mk_int srk 0) (mk_const srk step_noop);
                      mk_lt srk (mk_const srk step_noop) lc;
                      mk_not srk (mk_eq srk (mk_const srk step_focus) (mk_const srk step_noop));
                      neutralize_step_at step_noop])
                  (tbl_subst
                     srk
                     (mk_and 
                        srk 
                        (List.map 
                           (fun (z, z') -> mk_eq srk (mk_const srk z) (mk_const srk z'))
                           arr_projs))
                     intermediate_tbl))])
         (mk_exists_consts
            srk
            (fun sym -> not (List.mem sym inter_syms))
            (mk_and
               srk
               (neutralize_step_at step_focus ::
                tbl_subst srk proj_phi intermediate_tbl ::
                equalities))))

  let exp srk _ lc obj =
    let t1 = time "EXP IN" in
    let fresh_lc = mk_symbol srk `TyInt in (*this erases relation between lc and syms in iteration... not good*)
    let iter_proj = Iter.exp srk obj.iter_trs (mk_const srk fresh_lc) obj.iter_obj in
    let t3 = time "EXP first" in
    diff t1 t3 "EXP FIRST";
    to_file srk iter_proj "/Users/jakesilverman/Documents/duet/duet/ITER_PROJ2.smt2";
    let lc_syms = Symbol.Set.to_list (symbols lc) in
    let projed = Quantifier.mbp 
        srk 
        (fun sym -> List.mem sym (obj.proj_ind :: fresh_lc :: lc_syms @ (split_append obj.iter_trs)))
        iter_proj
    in
    to_file srk projed "/Users/jakesilverman/Documents/duet/duet/PROJED.smt2";
    to_file srk obj.projed_form "/Users/jakesilverman/Documents/duet/duet/PROJED2.smt2";
    let t4 = time "EXP SPEC PROJ" in
    diff t3 t4 "EXP SPEC PROJ";
    (* Clean up later to make use of transitionformula obj*)
    let noop_all_but_one = special_step srk obj.iter_trs (obj.projed_form) projed fresh_lc lc obj.new_trs obj.proj_ind in
    (*let noop_ground, _ = mbp_qe srk noop_all_but_one false in*)
    let noop_ground = noop_all_but_one in
    to_file srk noop_ground "/Users/jakesilverman/Documents/duet/duet/ITERPRENEW.smt2";  
    let noop_ground = Quantifier.miniscope srk noop_ground in
    let noop_ground = Quantifier.eq_guided_qe srk noop_ground in
    to_file srk noop_ground "/Users/jakesilverman/Documents/duet/duet/REWRITEGROUND.smt2";
    let noop_ground = Quantifier.mbp_qe_inplace srk noop_ground in
    to_file srk noop_ground "/Users/jakesilverman/Documents/duet/duet/GROUNDELIM.smt2";
    let t5 = time "EXP SEC" in
    diff t4 t5 "EXP SEC";
    let projed_right_lc = substitute_const srk (fun sym -> if compare_symbol sym fresh_lc = 0 then lc else mk_const srk sym) projed in
    let noop_eqs = 
      List.map 
        (fun (x, x') -> mk_eq srk (mk_const srk x) (mk_const srk x'))
        obj.iter_trs
    in
    let exp_res_pre = 
      mk_or 
        srk 
        [mk_and srk ((mk_eq srk lc (mk_int srk 0)) :: noop_eqs);
         mk_and srk [noop_ground; projed_right_lc]] 
    in
    let t6 = time "EXP TH" in
    diff t5 t6 "EXP TH";
    let map sym =  
      if sym = obj.proj_ind 
      then mk_var srk 0 `TyInt
      else if Hashtbl.mem obj.arr_map sym 
      then mk_select srk (mk_const srk (Hashtbl.find obj.arr_map sym)) 
          (mk_var srk 0 `TyInt) 
      else mk_const srk sym
    in
    let t7 = time "EXP SIX" in
    diff t6 t7 "EXP SIX";

    let substed = substitute_const srk map exp_res_pre in
    (*SrkSimplify.simplify_terms srk*) let res = (mk_forall srk `TyInt substed) in
    to_file srk res "/Users/jakesilverman/Documents/duet/duet/exp_phi.smt2";
    let t2 = time "EXP OUT" in
    diff t1 t2 "EXP";
    res



  let pp _ _ _= failwith "todo 10"

end

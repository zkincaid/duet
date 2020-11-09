open Syntax
open BatPervasives
open Iteration
module V = Linear.QQVector
module M = Linear.QQMatrix
module Z = Linear.ZZVector
module H = Abstract
include Log.Make(struct let name = "srk.array:" end)

(** Subsitute tbl[sym] for sym in phi for any sym that appears in tbl *)
let tbl_subst srk phi tbl = 
  substitute_const 
    srk 
    (fun sym -> BatHashtbl.find_default tbl sym (mk_const srk sym))
    phi

(* todo: figure out why the commented version causes infinite loop somewhere *)
let projection srk phi arr_tr_syms =
  let arr_map = Hashtbl.create (2 * (List.length arr_tr_syms)) in
  let j = mk_symbol srk ~name:"j" `TyInt in
  let j' = mk_symbol srk ~name:"j'" `TyInt in
  let phi = 
    mk_and 
      srk 
      [mk_eq srk (mk_const srk j) (mk_const srk j');
       phi]
  in
  let f (phi_proj_trs, phi_proj) (a, a') = 
    let z = mk_symbol srk ~name:"z"`TyInt in
    let z' = mk_symbol srk ~name:"z'" `TyInt in
    Hashtbl.add arr_map z a;
    Hashtbl.add arr_map z' a';
    (z, z') :: phi_proj_trs,
    mk_and
      srk
      [mk_forall srk `TyInt
         (mk_if 
            srk 
            (mk_eq srk (mk_var srk 0 `TyInt) (mk_const srk j))
            (mk_and 
               srk 
               [mk_eq srk (mk_const srk z) (mk_app srk a [mk_var srk 0 `TyInt]);
                mk_eq srk (mk_const srk z') (mk_app srk a' [mk_var srk 0 `TyInt])]));
       phi_proj]
    (*mk_and 
      srk 
      [mk_eq srk (mk_const srk z) (mk_app srk a [mk_const srk j]);
       mk_eq srk (mk_const srk z') (mk_app srk a' [mk_const srk j]);
       phi_proj]*)
  in
  (j, j'), arr_map, List.fold_left f ([(j, j')], phi) arr_tr_syms

(* Assumes only two sorts, int and int -> int*)
let separate_symbols_by_sort srk tr_symbols =
  List.partition (fun (s, _) -> typ_symbol srk s = `TyInt) tr_symbols

let get_arr_syms srk phi =
  let symbols = Syntax.symbols phi in
  Symbol.Set.filter (fun sym -> not (typ_symbol srk sym = `TyInt)) symbols

let to_mfa srk (phi : 'a formula) =
  let skolemtbl = Hashtbl.create 100 in
  (* skolemize every exist quant that has no preceding universal var quant *)
  let rec skolem_exists_head depth univ_depth srk expr =
    match destruct srk expr with
    | `Var (i, `TyInt) ->
      if Option.is_none univ_depth || depth - i < Option.get univ_depth
      then Some (Hashtbl.find skolemtbl (depth - i - 1))
      else Some (mk_var srk i `TyInt)
    | `Quantify (`Forall, name, `TyInt, phi) ->
      if Option.is_some univ_depth then 
        failwith "Nested univ quant in row not in PMFA fragment"
      else (
        let depth' = depth + 1 in
        let phi' = custom_eval srk (skolem_exists_head depth' (Some depth')) phi in
        Some (mk_forall srk ~name:name `TyInt phi'))
    | `Quantify (`Exists, name, `TyInt, phi) ->
        Hashtbl.add skolemtbl depth (mk_const srk (mk_symbol srk ~name:name `TyInt));
        let res = custom_eval srk (skolem_exists_head (depth + 1) univ_depth) phi in
        Hashtbl.remove skolemtbl depth;
        Some res
    | _ -> None
  in
  let phi = custom_eval srk (skolem_exists_head 0 None) phi in
  let disj bool_list = List.fold_left (||) false bool_list in
  (* merge univ quant so just a single univ quant *)
  let alg = function
    | `Quantify (`Forall, _, `TyInt, (false, phi)) -> true, phi
    | `Or disjuncts -> 
      let has_univs, _ = List.split disjuncts in
      let fresh = mk_symbol srk `TyInt in
      let f ind (has_univ, phi) =
        if has_univ then  
           mk_and srk [phi; mk_eq srk (mk_const srk fresh) (mk_int srk ind)]
        else phi
      in
      disj has_univs, mk_or srk (List.mapi f disjuncts)
    | `Tru -> false, mk_true srk
    | `Fls -> false, mk_false srk
    | `Atom a -> false, Formula.construct srk (`Atom a)
    | `And conjuncts ->
      let has_univs, phis = List.split conjuncts in
      disj has_univs, mk_and srk phis
    | `Ite ((false, cond), (has_univ2, bthen), (has_univ3, belse)) -> 
      has_univ2 || has_univ3, mk_ite srk cond bthen belse
    | `Not (false, phi) -> false, mk_not srk phi
    | _ -> failwith "not in scope of logical fragment"
  in
  let _, matr = Formula.eval srk alg phi in
  (* observe that the leading univ quant not added back yet *)
  mk_forall srk `TyInt matr

(* we assume mfa formula have just a single (universal) quantifier. *)
let mfa_to_lia srk matrix =
  let matrix = 
    match destruct srk matrix with
    | `Quantify (`Forall, _, `TyInt, matrix) -> matrix
    | _ -> failwith "mfa formula needs to start with leading univ quant"
  in
  let uquant_depth' = Symbol.Set.cardinal (get_arr_syms srk matrix) in
  let arrcounter = ref 0 in
  let symread_to_numsym =
    Memo.memo (fun _ -> 
        arrcounter := !arrcounter + 1;
        mk_var srk (!arrcounter - 1) `TyInt)
  in
  let termreads : (symbol, 'a term) Hashtbl.t = Hashtbl.create 100 in
  let termread_to_numsym : 'c * 'd -> 'a term =
    Memo.memo (fun (arrsym, readterm) -> 
        Hashtbl.add termreads arrsym readterm;
        mk_const srk (mk_symbol srk `TyInt))
  in
  let rec termalg = function
    | `App (arrsym, [readterm]) ->
      let readterm = Expr.term_of srk readterm in
      begin match destruct srk readterm with
      | `Var (0, `TyInt) -> symread_to_numsym arrsym 
      | `Var _ -> failwith "mfa formula should only have single bound var"
      | _ -> (termread_to_numsym (arrsym, readterm) :> ('a, typ_arith) expr)
      end
    | `Var (0, `TyInt) -> mk_var srk uquant_depth' `TyInt
    | `Var _ -> failwith "mfa formula should only have single bound var"
    | `Ite (cond, bthen, belse) -> (*TODO: confirm right*)Log.errorf "\n\nTERMCONDCOND is%a" (Formula.pp srk) cond;
      mk_ite srk (Formula.eval srk formalg cond) bthen belse
    | open_term -> Term.construct srk open_term 
  
  and formalg = function
    | `Atom (`Eq, x, y) -> 
      mk_eq srk (Term.eval srk termalg x) (Term.eval srk termalg y)
    | `Atom (`Leq, x, y) -> 
      mk_leq srk (Term.eval srk termalg x) (Term.eval srk termalg y)
    | `Atom (`Lt, x, y) -> 
      mk_lt srk (Term.eval srk termalg x) (Term.eval srk termalg y)
    | open_formula -> Formula.construct srk open_formula
  in
  let matrix : 'a formula = Formula.eval srk formalg matrix in
  let functional_consistency_clauses =
    List.map (fun (arrsym, readterm) ->
        (* figure out how to not have to cast this *)
        mk_if 
          srk 
          (mk_eq srk (mk_var srk uquant_depth' `TyInt) readterm)
          (mk_eq 
             srk 
             (symread_to_numsym arrsym) 
             (termread_to_numsym (arrsym, readterm))))
      (BatHashtbl.to_list termreads)
  in
  let matrix = mk_and srk (matrix :: functional_consistency_clauses) in
  let phi = 
    BatEnum.fold 
      (fun phi _ -> mk_exists srk ~name:"_" `TyInt phi) 
      matrix
      (0--(uquant_depth' - 1))
  in
  mk_forall srk `TyInt phi

let mbp_qe srk phi =
  let qp, matr = Quantifier.normalize srk phi in
  let remove_quant quant_typ syms matr =
    if quant_typ = None then matr
    else if Option.get quant_typ = `Forall then
      mk_not srk (Quantifier.mbp srk (fun sym -> not (List.mem sym syms)) (mk_not srk matr))
    else Quantifier.mbp srk (fun sym -> not (List.mem sym syms))  matr
  in
  let qt, syms, matr = 
    List.fold_right
      (fun (qt, sym) (quant_typ, syms, matr) ->
         if quant_typ = None then (Some qt, [sym], matr)
         else if Option.get quant_typ = qt then (quant_typ, sym :: syms, matr)
         else (Some qt, [sym], remove_quant quant_typ syms matr))
      qp
      (None, [], matr)
  in
  remove_quant qt syms matr

let pmfa_to_lia srk pmfa = mfa_to_lia srk (to_mfa srk pmfa)

let merge_proj_syms srk trs1 trs2 =
  let f (x, x') (y, y') = 
    mk_eq srk (mk_const srk x) (mk_const srk y), 
    (mk_eq srk (mk_const srk x') (mk_const srk y'))
  in
  let eqs = BatList.map2 f trs1 trs2 in
  let a, b = List.split eqs in
  a @ b

let is_eq_projs srk phi1 phi2 tr =
  let _, _, (trs1, phi1_proj) = projection srk phi1 tr in
  let _, _, (trs2, phi2_proj) = projection srk phi2 tr in
  let phi1_proj_lia = mk_forall srk `TyInt (pmfa_to_lia srk phi1_proj) in
  let phi2_proj_lia = mk_forall srk `TyInt (pmfa_to_lia srk phi2_proj) in
  let consistency_syms = merge_proj_syms srk trs1 trs2 in
  let phi = mk_and srk (phi1_proj_lia :: consistency_syms) in
  let psi = mk_and srk (phi2_proj_lia :: consistency_syms) in
  let equiv =   mk_or srk [mk_and srk [phi; mk_not srk psi];
               mk_and srk [mk_not srk phi; psi]] in
  match Quantifier.simsat srk equiv with
  | `Sat -> `No
  | `Unsat -> `Yes
  | `Unknown -> `Unknown

let lift srk (proj, proj') arr_map phi =
  let map sym =  
    if sym = proj || sym = proj' 
    then mk_var srk 0 `TyInt
    else if Hashtbl.mem arr_map sym 
    then mk_app srk (Hashtbl.find arr_map sym) [mk_var srk 0 `TyInt] 
    else mk_const srk sym
  in
  mk_forall srk `TyInt (substitute_const srk map phi)


 

    
module Array_analysis (Iter : PreDomain) = struct

  type 'a t = 
    { iter_obj : 'a Iter.t; 
      proj_inds : Symbol.t * Symbol.t; 
      arr_map : (Symbol.t, Symbol.t) Hashtbl.t;
      new_trs : (Symbol.t * Symbol.t) list;
      iter_trs : (Symbol.t * Symbol.t) list;
      projed_form : 'a TransitionFormula.t}
  
  (* TODO:Clean up and actually use tf*)
  let abstract srk tf =
    let exists = TransitionFormula.exists tf in
    let tr_symbols = TransitionFormula.symbols tf in
    let phi = TransitionFormula.formula tf in
    Log.errorf "\n\nFORMuLA IS %a" (Formula.pp srk) phi;
    let num_trs, arr_trs = separate_symbols_by_sort srk tr_symbols in 
    let proj_inds, arr_map, (new_trs, phi_proj) = projection srk phi arr_trs in
    let matrix = to_mfa srk phi_proj in
    let lia = mfa_to_lia srk matrix in
    let iter_trs = num_trs@new_trs in
    let ground = TransitionFormula.make ~exists (mbp_qe srk lia) iter_trs in
    {iter_obj=Iter.abstract srk ground;
     proj_inds;
     arr_map;
     new_trs;
     iter_trs;
     projed_form=ground}


  (*let equal _ _ _ _= failwith "todo 5"

  let widen _ _ _ _= failwith "todo 6"

  let join _ _ _ _ = failwith "todo 7"
*)
  let split_append lst = 
    let a, b = List.split lst in
    a @ b

  let special_step srk int_trs proj_phi proj_phi_exp temp_lc_sym lc arr_projs =
    let step_focus = mk_symbol srk ~name:"s" `TyInt in
    let step_noop = mk_symbol srk ~name:"p" `TyInt in
    let pre_tbl = Hashtbl.create (List.length int_trs) in
    let post_tbl = Hashtbl.create (List.length int_trs) in
    let intermediate_tbl = Hashtbl.create (2*(List.length int_trs)) in
    let inter_syms = ref [] in
    List.iter
      (fun (sym, sym') -> 
         let fresh_copy sym = mk_symbol srk ~name:((show_symbol srk sym)^"''") `TyInt in
         let sym'' = fresh_copy sym in
         let sym''' = fresh_copy sym' in
         inter_syms := sym'' :: sym''' :: !inter_syms;
         Hashtbl.add pre_tbl sym' (mk_const srk sym'');
         Hashtbl.add intermediate_tbl sym (mk_const srk sym'');
         Hashtbl.add intermediate_tbl sym' (mk_const srk sym''');
         Hashtbl.add post_tbl sym (mk_const srk sym'''))
      int_trs;
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
    let fresh_lc = mk_symbol srk `TyInt in (*this erases relation between lc and syms in iteration... not good*)
    let iter_proj = Iter.exp srk obj.iter_trs (mk_const srk fresh_lc) obj.iter_obj in
    let lc_syms = Symbol.Set.to_list (symbols lc) in
    let projed = Quantifier.mbp 
        srk 
        (fun sym -> List.mem sym (fresh_lc :: lc_syms @ (split_append obj.iter_trs)))
        iter_proj
    in
    (* Clean up later to make use of transitionformula obj*)
    let noop_all_but_one = special_step srk obj.iter_trs (TransitionFormula.formula obj.projed_form) projed fresh_lc lc obj.new_trs in
    let noop_ground = mbp_qe srk noop_all_but_one in
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
    let map sym =  
      if sym = fst obj.proj_inds || sym = snd obj.proj_inds 
      then mk_var srk 0 `TyInt
      else if Hashtbl.mem obj.arr_map sym 
      then mk_app srk (Hashtbl.find obj.arr_map sym) [mk_var srk 0 `TyInt] 
      else mk_const srk sym
    in
    let substed = substitute_const srk map exp_res_pre in
    (*SrkSimplify.simplify_terms srk*) (mk_forall srk `TyInt substed)


  let pp _ _ _= failwith "todo 10"

end

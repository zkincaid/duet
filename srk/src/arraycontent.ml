open Syntax
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

let to_mfa srk (phi : 'a formula) =
  let skolemtbl = Hashtbl.create 100 in
  let rec skolemize srk args expr =
    let depth = Option.get (List.hd args) in
    let univ_depth = List.nth args 1 in
    match destruct srk expr with
    | `Var (i, `TyInt) ->
      if Option.is_none univ_depth || depth - i < Option.get univ_depth
      then Some (Hashtbl.find skolemtbl (depth - i - 1))
      else Some (mk_var srk i `TyInt)
    | `Quantify (`Forall, name, `TyInt, phi) ->
      Some (mk_forall srk ~name:name `TyInt (custom_eval srk [Some (depth + 1); Some (depth + 1)] skolemize phi))
    | `Quantify (`Exists, _, `TyInt, phi) ->
        Hashtbl.add skolemtbl depth (mk_const srk (mk_symbol srk `TyInt));
        let res = custom_eval srk [Some (depth + 1); univ_depth] skolemize phi in
        Hashtbl.remove skolemtbl depth;
        Some res
    | _ -> None
  in
  let phi = custom_eval srk [Some 0; None] skolemize phi in
  let disj bool_list = List.fold_left (||) false bool_list in
  let alg = function
    | `Quantify (`Forall, _, `TyInt, (false, phi)) -> true, phi
    | `Or disjuncts -> 
      let qfvs, _ = List.split disjuncts in
      let fresh = mk_symbol srk `TyInt in
      let f ind (qfv, phi) =
        if qfv then  
           mk_and srk [phi; mk_eq srk (mk_const srk fresh) (mk_int srk ind)]
        else phi
      in
      disj qfvs, mk_or srk (List.mapi f disjuncts)
    | `Tru -> false, mk_true srk
    | `Fls -> false, mk_false srk
    | `Atom (`Eq, x, y) -> false,  mk_eq srk x y
    | `Atom (`Leq, x, y) -> false,  mk_leq srk x y
    | `Atom (`Lt, x, y) -> false,  mk_lt srk x y
    | `And conjuncts ->
      let qfvs, phis = List.split conjuncts in
      disj qfvs, mk_and srk phis
    | `Ite ((false, cond), (qfv2, bthen), (qfv3, belse)) -> qfv2 || qfv3, mk_ite srk cond bthen belse
    | `Not (false, phi) -> false, mk_not srk phi          
    |`Proposition (`App (p, [expr])) ->
      begin match Expr.refine srk expr with
        | `Term t -> false, mk_app srk p [t]
        | _ -> failwith "not in scope of logical fragment"
      end
    | _ -> failwith "not in scope of logical fragment"
  in
  let _, matr = Formula.eval srk alg phi in
  let matr = (matr :> 'a formula) in
  matr

let mfa_to_lia srk matrix =
  let const_reads = Hashtbl.create 100 in
  let univ_reads = Hashtbl.create 100 in
  let temp_univ_sym = mk_symbol srk `TyInt in 
  let termalg = function
    | `App (arrsym, [readterm]) ->
      begin match destruct srk readterm with
        | `Var (_, `TyInt) ->
          if not (Hashtbl.mem univ_reads arrsym) then
            Hashtbl.add univ_reads arrsym (Hashtbl.length univ_reads) else ();
          mk_var srk (Hashtbl.find univ_reads arrsym) `TyInt
        | `App (const, []) -> 
          if not (Hashtbl.mem const_reads (arrsym, const)) then
            Hashtbl.add const_reads (arrsym, const) (mk_symbol srk `TyInt) else ();
          mk_const srk (Hashtbl.find const_reads (arrsym, const))
        | _ -> failwith "not flat"
      end
    | `Var (_, `TyInt) -> mk_const srk temp_univ_sym
    | open_term -> Term.construct srk open_term 
  in
  let formalg = function
    | `Atom (`Eq, x, y) -> mk_eq srk (Term.eval srk termalg x) (Term.eval srk termalg y)
    | `Atom (`Leq, x, y) -> mk_leq srk (Term.eval srk termalg x) (Term.eval srk termalg y)
    | `Atom (`Lt, x, y) -> mk_lt srk (Term.eval srk termalg x) (Term.eval srk termalg y)
    | `Proposition (`App (p, [expr])) ->
      begin match Expr.refine srk expr with
        | `Term t -> 
          let term = Term.eval srk termalg t in
          mk_app srk p [term]
        | _ -> failwith "not in scope of logical fragment"
      end
    | open_formula -> Formula.construct srk open_formula
  in
  let matrix : 'a formula = Formula.eval srk formalg matrix in
  let uquant_depth = Hashtbl.length univ_reads in
  let subst_for_univ_sym sym = 
    if sym = temp_univ_sym 
    then mk_var srk uquant_depth `TyInt 
    else mk_const srk sym
  in
  let matrix = substitute_const srk subst_for_univ_sym matrix in
  let both_reads = 
    BatHashtbl.filteri 
      (fun (arrsym, _) _ -> Hashtbl.mem univ_reads arrsym) 
      const_reads 
  in
  let add_consistency_clause (arrsym, readsym) new_sym conjuncts =
    let conjunct = 
      mk_if 
        srk 
        (mk_eq srk (mk_var srk uquant_depth `TyInt) (mk_const srk readsym))
        (mk_eq srk (mk_var srk (Hashtbl.find univ_reads arrsym) `TyInt) (mk_const srk new_sym))
    in
    conjunct :: conjuncts
  in
  let consistency_conjs = Hashtbl.fold add_consistency_clause both_reads [] in
  let matrix = mk_and srk (matrix :: consistency_conjs) in
  let phi = 
    Hashtbl.fold 
      (fun _ _ phi -> mk_exists srk ~name:"_" `TyInt phi) 
      univ_reads 
      matrix
  in
  phi

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
  Log.errorf "\n\n\nphi is %a" (Formula.pp srk) phi;
  (*let imp = mk_not srk (mk_if srk phi psi) in*)
  let equiv =   mk_or srk [mk_and srk [phi; mk_not srk psi];
               mk_and srk [mk_not srk phi; psi]] in
  Syntax.to_file srk equiv "/Users/jakesilverman/Documents/duet/duet/equiv.smt2"; 
  Smt.equiv 
    srk 
    (mk_and srk (phi1_proj_lia :: consistency_syms)) 
    (mk_and srk (phi2_proj_lia :: consistency_syms))


    
module Array_analysis (Iter : PreDomain) = struct

  type 'a t = 
    { iter_obj : 'a Iter.t; 
      proj_inds : Symbol.t * Symbol.t; 
      arr_map : (Symbol.t, Symbol.t) Hashtbl.t;
      new_trs : (Symbol.t * Symbol.t) list;
      iter_trs : (Symbol.t * Symbol.t) list;
      projed_form : 'a formula}
    
  let abstract ?(exists=fun _ -> true) srk tr_symbols phi =
    let num_trs, arr_trs = separate_symbols_by_sort srk tr_symbols in 
    let proj_inds, arr_map, (new_trs, phi_proj) = projection srk phi arr_trs in
    let matrix = to_mfa srk phi_proj in
    Log.errorf "%b" (exists (fst (List.hd tr_symbols)));
    let lia = mfa_to_lia srk matrix in
    let iter_trs = num_trs@new_trs in
    let lia = mk_forall srk `TyInt lia in
    Log.errorf "proj os %a" (Formula.pp srk) lia;
    let ground = mbp_qe srk lia in
    {iter_obj=Iter.abstract ~exists srk iter_trs ground;
     proj_inds;
     arr_map;
     new_trs;
     iter_trs;
     projed_form=ground}


  let equal _ _ _ _= failwith "todo 5"

  let widen _ _ _ _= failwith "todo 6"

  let join _ _ _ _ = failwith "todo 7"

  let split_append lst = 
    let a, b = List.split lst in
    a @ b

  let special_step srk int_trs proj_phi proj_phi_exp temp_lc_sym lc arr_projs =
    let mk_forall_const_lst srk lst phi = List.fold_left (fun phi const -> mk_forall_const srk const phi) phi lst in
    let mk_exists_const_lst srk lst phi = List.fold_left (fun phi const -> mk_exists_const srk const phi) phi lst in
    let step = mk_symbol srk ~name:"s" `TyInt in
    let step_other = mk_symbol srk ~name:"p" `TyInt in
    let pre_tbl : (symbol, ('a, 'c) expr) Hashtbl.t = Hashtbl.create (List.length int_trs) in
    let post_tbl : (symbol, ('a, 'c) expr) Hashtbl.t = Hashtbl.create (List.length int_trs) in
    let intermediate_tbl : (symbol, ('a, 'c) expr) Hashtbl.t = Hashtbl.create (2*(List.length int_trs)) in
    let inter_syms = ref [] in
    List.iter
      (fun (sym, sym') -> 
         let add'' sym = 
           (*if symbol_name srk sym = None then mk_symbol srk `TyInt
           else*) 
             mk_symbol 
               srk 
               ~name:((show_symbol srk sym)^"''") 
               `TyInt 
         in
         let sym'' : symbol = add'' sym in
         let sym''' : symbol = add'' sym' in
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
      step
      (mk_if
         srk
         (mk_and
            srk
            [mk_leq srk (mk_int srk 0) (mk_const srk step);
             mk_lt srk (mk_const srk step) lc;
             mk_forall_const_lst
               srk
               (step_other :: inter_syms)
               (mk_if
                  srk
                  (mk_and
                     srk
                     [mk_leq srk (mk_int srk 0) (mk_const srk step_other);
                      mk_lt srk (mk_const srk step_other) lc;
                      mk_not srk (mk_eq srk (mk_const srk step) (mk_const srk step_other));
                      neutralize_step_at step_other])
                  (tbl_subst
                     srk
                     (mk_and 
                        srk 
                        (List.map 
                           (fun (z, z') -> mk_eq srk (mk_const srk z) (mk_const srk z'))
                           arr_projs))
                     intermediate_tbl))])
         (mk_exists_const_lst
            srk
            inter_syms
            (mk_and
               srk
               (neutralize_step_at step ::
                tbl_subst srk proj_phi intermediate_tbl ::
                equalities))))

  let exp srk _ lc obj =
    let fresh_lc = mk_symbol srk `TyInt in (*this erases relation between lc and syms in iteration... not good*)
    let iter_proj = Iter.exp srk obj.iter_trs (mk_const srk fresh_lc) obj.iter_obj in
    Log.errorf "\n\nexp form is is %a" (Formula.pp srk) iter_proj;
    let lc_syms = Symbol.Set.to_list (symbols lc) in
    let projed = Quantifier.mbp 
        srk 
        (fun sym -> List.mem sym (fresh_lc :: lc_syms @ (split_append obj.iter_trs)))
        iter_proj
    in
    let noop_all_but_one = special_step srk obj.iter_trs obj.projed_form projed fresh_lc lc obj.new_trs in
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
    Log.errorf "failure2";
    let map sym =  
      if sym = fst obj.proj_inds || sym = snd obj.proj_inds 
      then mk_var srk 0 `TyInt
      else if Hashtbl.mem obj.arr_map sym 
      then mk_app srk (Hashtbl.find obj.arr_map sym) [mk_var srk 0 `TyInt] 
      else mk_const srk sym
    in
    Log.errorf "failure3";
    let substed = substitute_const srk map exp_res_pre in
    Log.errorf "failure4";
    Syntax.to_file srk noop_ground  "/Users/jakesilverman/Documents/duet/duet/projed_form.smt2"; 
    (*SrkSimplify.simplify_terms srk*) (mk_forall srk `TyInt substed)


  let pp _ _ _= failwith "todo 10"

end

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
  List.filter 
    (fun (s, _) -> typ_symbol srk s = `TyFun([`TyInt], `TyInt))
    (T.symbols tf)
let fo_trs srk tf =
  List.filter 
    (fun (s, _) -> 
       (typ_symbol srk s = `TyInt) ||
       (typ_symbol srk s = `TyReal) ||
       (typ_symbol srk s = `TyBool))
    (T.symbols tf)


module Bitbl = struct
  type ('a, 'b) t = ('a, 'b) Hashtbl.t * ('b, 'a) Hashtbl.t
  let create size = Hashtbl.create size, Hashtbl.create size
  let mem (tbl, _) a = Hashtbl.mem tbl a
  let rev_mem (_, inv) b = Hashtbl.mem inv b
  let add (tbl, inv) a b =
    if Hashtbl.mem tbl a || Hashtbl.mem inv b then
      failwith "Attempted to add matched element to bimap"
    else (Hashtbl.add tbl a b; Hashtbl.add inv b a)
  let find (tbl, _) a = Hashtbl.find tbl a
  let rev_find (_, inv) b = Hashtbl.find inv b
end

(** Subsitute tbl[sym] for sym in phi for any sym that appears in tbl *)
let tbl_subst srk phi tbl = 
  substitute_const 
    srk 
    (fun sym -> BatHashtbl.find_default tbl sym (mk_const srk sym))
    phi

let projection srk tf =
  let map = Hashtbl.create (List.length (arr_trs srk tf) * 8 / 3) in
  let j = mk_symbol srk ~name:"j" `TyInt in
  let f (trs, phi_proj) (a, a') = 
    let z = mk_symbol srk ~name:"z"`TyInt in
    let z' = mk_symbol srk ~name:"z'" `TyInt in
    Hashtbl.add map z a;
    Hashtbl.add map z' a';
    (z, z') :: trs,
    mk_and 
      srk 
      [mk_eq srk (mk_const srk z) (mk_app srk a [mk_const srk j]);
       mk_eq srk (mk_const srk z') (mk_app srk a' [mk_const srk j]);
       phi_proj]
  in
  let trs, phi' = 
    List.fold_left f ((j, j) :: fo_trs srk tf, T.formula tf) (arr_trs srk tf) 
  in
  j, map, T.make ~exists:(T.exists tf) phi' trs 


let get_arr_syms srk phi =
  let symbols = Syntax.symbols phi in
  Symbol.Set.filter (fun sym -> not (typ_symbol srk sym = `TyInt)) symbols

let to_mfa srk tf =
  to_file srk (T.formula tf) "/Users/jakesilverman/Documents/duet/duet/MFAenter.smt2" ; 
  let rec partial_skolemization expr skolem_lst =
    let f expr = partial_skolemization expr skolem_lst in
    match Formula.destruct srk expr with
    | `Quantify (`Exists, name, `TyInt, phi) ->
      partial_skolemization 
        phi
        ((mk_const srk (mk_symbol srk ~name `TyInt)) :: skolem_lst)
    | `And conjuncts -> 
      mk_and srk (List.map (fun conj -> f conj) conjuncts)
    | `Or disjuncts ->
      mk_or srk (List.map (fun disj -> f disj) disjuncts)
    | open_form ->
      substitute
        srk
        (fun i -> List.nth skolem_lst i)
        (Formula.construct srk open_form)
  in
  let phi = partial_skolemization (T.formula tf) [] in
  to_file srk (phi) "/Users/jakesilverman/Documents/duet/duet/MFA2.smt2" ;   
  let rec merge_univ expr disj_syms =
    match Formula.destruct srk expr with
    | `Quantify (`Forall, _, `TyInt, phi) ->
      let merge_equalities =
        List.map 
          (fun (ind, sym) -> mk_eq srk (mk_const srk sym) (mk_int srk ind))
          disj_syms
      in
      mk_and srk (phi :: merge_equalities) 
    | `And conjuncts -> 
      mk_and srk (List.map (fun conj -> merge_univ conj disj_syms) conjuncts)
    | `Or disjuncts ->
      let sym = mk_symbol srk `TyInt in
      mk_or 
        srk 
        (List.mapi 
           (fun ind disj -> merge_univ disj ((ind, sym) :: disj_syms))
           disjuncts)
    | open_form -> Formula.construct srk open_form
  in
  let matr = merge_univ phi [] in
  (* TODO: return tf... maybe do sanity check*)
  let res = mk_forall srk `TyInt matr in
  to_file srk res "/Users/jakesilverman/Documents/duet/duet/MFAexi.smt2" ; 
  res
 

let flatten syms = List.fold_left (fun acc (sym, sym') -> sym :: sym' :: acc) [] syms 



(* we assume mfa formula have just a single (universal) quantifier. *)
let mfa_to_lia srk matrix free_num_syms =
  to_file srk matrix "/Users/jakesilverman/Documents/duet/duet/PRELIA.smt2" ;  
  let matrix = 
    match destruct srk matrix with
    | `Quantify (`Forall, _, `TyInt, matrix) -> matrix
    | _ -> failwith "mfa formula needs to start with leading univ quant"
  in
  let fresh = mk_symbol srk `TyInt in
  let freshs = mk_const srk fresh in
  let arr_syms = get_arr_syms srk matrix in
  let matr = substitute srk (fun deb -> if deb = 0 then freshs else assert false) matrix in

  let uquant_depth' = Symbol.Set.cardinal arr_syms in
  let arrcounter = ref 0 in
  let symread_to_numsym =
    Memo.memo (fun _ -> 
        arrcounter := !arrcounter + 1;
        let sym = mk_symbol srk ~name:"SYMREAD"`TyInt in
        sym)
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
      if Expr.equal readterm  freshs then
        (mk_const srk (symread_to_numsym arrsym))
      else (termread_to_numsym (arrsym, readterm) :> ('a, typ_arith) expr)
    | `Ite (cond, bthen, belse) -> (*TODO: confirm right*)
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
  let matrix : 'a formula = Formula.eval srk formalg matr in
  let functional_consistency_clauses =
    List.map (fun (arrsym, readterm) ->
        (* figure out how to not have to cast this *)
        mk_if 
          srk 
          (mk_eq srk freshs readterm)
          (mk_eq 
             srk 
             (mk_const srk (symread_to_numsym arrsym)) 
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
  let arrsymreads = Symbol.Set.map (fun ele -> let res = symread_to_numsym ele in res) arr_syms in
  let phi' = mk_exists_consts srk (fun sym -> not (Symbol.Set.mem sym arrsymreads)) phi in
  to_file srk phi' "/Users/jakesilverman/Documents/duet/duet/PENTULTLIA.smt2" ;
  List.iter (fun sym -> Log.errorf "sym is %a" (pp_symbol srk) sym) (flatten free_num_syms);
  let res = mk_exists_consts srk (fun sym -> List.mem sym (flatten free_num_syms)) (mk_forall_const srk fresh phi') in
  to_file srk res "/Users/jakesilverman/Documents/duet/duet/POSTLIA.smt2" ; 
  res
 

let mbp_qe ?(flag = false) srk phi head =
  let t1 = time "Enter MBP" in
  let qp, matr = Quantifier.normalize srk phi in
  (if flag then (Log.errorf "\nMBP1\n") else ());
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
  let res = 
    if head then
    match qt with
    | None -> matr, []
    | Some `Exists -> matr, syms
    | Some `Forall -> remove_quant qt syms matr, []
    else remove_quant qt syms matr, []
  in
  let t2 = time "EXIT MBP" in
  diff t1 t2 "MBP"; res

(*let pmfa_to_lia srk pmfa syms = mfa_to_lia srk (to_mfa srk pmfa) syms*)

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
    let tf = T.make ~exists:(T.exists tf) (T.formula tf) tr_symbols in
    let proj_ind, arr_map, tf_proj = projection srk tf in
    let matrix = to_mfa srk tf_proj in
    let iter_trs = T.symbols tf_proj in
    let lia = mfa_to_lia srk matrix iter_trs in
    let new_trs = List.filter (fun a -> not (List.mem a tr_symbols)) iter_trs in
    let ground, new_consts = mbp_qe ~flag:!flag srk lia true in
    let exists = fun sym -> (not (List.mem sym new_consts)) && exists sym in
    let ground_tf = TransitionFormula.make ~exists ground  iter_trs in
    let iter_obj = Iter.abstract srk ground_tf in
    let projed_form = mk_exists_consts srk (fun sym -> not (List.mem sym new_consts)) ground in
    let t2 = time "EXIT abstract" in
    diff t1 t2 "ABSTRACT";
    {iter_obj;
     proj_ind;
     arr_map;
     new_trs;
     iter_trs;
     projed_form;
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
    let t4 = time "EXP SPEC PROJ" in
    diff t3 t4 "EXP SPEC PROJ";
    (* Clean up later to make use of transitionformula obj*)
    let noop_all_but_one = special_step srk obj.iter_trs (obj.projed_form) projed fresh_lc lc obj.new_trs obj.proj_ind in
    (*let noop_ground, _ = mbp_qe srk noop_all_but_one false in*)
    let noop_ground = noop_all_but_one in
    to_file srk noop_ground "/Users/jakesilverman/Documents/duet/duet/ITERPRENEW.smt2";   
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
         mk_and srk [(*noop_ground;*) projed_right_lc]] 
    in
    let t6 = time "EXP TH" in
    diff t5 t6 "EXP TH";
    let map sym =  
      if sym = obj.proj_ind 
      then mk_var srk 0 `TyInt
      else if Hashtbl.mem obj.arr_map sym 
      then mk_app srk (Hashtbl.find obj.arr_map sym) [mk_var srk 0 `TyInt] 
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

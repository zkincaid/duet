open Syntax
open BatPervasives
module V = Linear.QQVector
module M = Linear.QQMatrix
module Z = Linear.ZZVector
module H = Abstract
include Log.Make(struct let name = "srk.mdvas" end)

(* A transformer defines an affine transition
 * X' = X diag(a) + b. "a" is {0, 1}^n, and b
 * is Q^n.
 *)
type transformer =
  { a : Z.t;
    b : V.t }
[@@deriving ord, show]


(* Figure out way to clean up these types a bit *)
module Transformer = struct
  type t = transformer 
  [@@deriving ord, show]
end

module TSet = BatSet.Make(Transformer)

type vas = TSet.t

let pp_vas formatter (vas : vas) : unit =
  SrkUtil.pp_print_enum pp_transformer formatter (TSet.enum vas)  

(* A VAS abstraction contains a set of transformers, v,
 * a list of linear simulations matrices, S_lst,
 * a set of invariants, invars,
 * and _____.
 *
 * Each matrix in S_lst starts at the 0th row. Unify
 * is used to stack the elements in S_lst together for
 * use with transformers.The first row of the first item
 * in S_lst is matched with the first row of "a" and "b"
 * in a given transformer.
 *
 * There is exactly one item in S_lst for each coherence class
 * of v. A coherence class is defined as a set of rows that
 * reset together in every transformer.
 *
 * invars is a list of invariants that hold after a single
 * transition, and every transition thereafter. invars is
 * used to remove variables from the formula. For instance,
 * if x'= 3 is an invariant, we can substitute in 3 for x'
 * when computing the transformers and just add this fact
 * in during the closure.
 *
 * ____ is an optimization related to invariants. There
 * are certain invariants that, when taken together, restrict
 * the transition system to running at most once
 * (for example, x' = 1 and x = x + 1).
 *)
type 'a t = { v : vas; alphas : M.t list; invars : 'a formula list; invarmaxk : bool}


let mk_top = {v=TSet.empty; alphas=[]; invars=[]; invarmaxk=false}

(* This function is used to stack the matrices in S_lst
 * on top of each other. Each matrix in S_lst must start at
 * row 0. The matrices are stacked sequentially, with the first
 * matrix in S_lst corresponding to the first rows of the output matrix.
 * This function is primarily used to relate the dynamics matrix 
 * (S, equiv S_lst stacked on each other) to the transformers.
 *)
let unify (alphas : M.t list) : M.t =
  let unified = List.fold_left (fun matrix alphacell -> 
      BatEnum.fold (fun matrix (_, vector) ->
          M.add_row (M.nb_rows matrix) vector matrix) 
        matrix 
        (M.rowsi alphacell))
      M.zero alphas in
  unified

let unify_vects (vects : V.t list) : V.t =
  let unified = List.fold_left (fun accvec v -> 
      BatEnum.fold (fun accvec (ele, _) ->
          V.add_term ele (BatEnum.count (V.enum accvec)) accvec) 
        accvec 
        (V.enum v))
      V.zero vects in
  unified




(* Used in preify and postify to create symbol map.
 * Is a way to substitute variables; for example
 * x with x' or x' with x.
 *)
let post_map srk tr_symbols =
  List.fold_left
    (fun map (sym, sym') -> Symbol.Map.add sym (mk_const srk sym') map)
    Symbol.Map.empty
    tr_symbols

(* preify takes in the context, the symbol tuple list, and a term.
 * If symbol tuple list is of form (x, x'), as in tr_symbols,
 * replace x' with x in term.
 *)
let preify srk tr_symbols = substitute_map srk (post_map srk (List.map (fun (x, x') -> (x', x)) tr_symbols))

(* Same as preify, but replaces x with x' *)
let postify srk tr_symbols = substitute_map srk (post_map srk tr_symbols)

(* 1 kvar for each transformer; 1 svar per row in equiv class; 1 rvar, 1 kstack for each equiv class*)
let create_exp_vars srk alphas num_trans =
  let bdim = ref 0 in
  let rec create_k_ints k vars basename equiv_num (arttype : Syntax.typ) =
    begin match k <= 0 with
      | true -> List.rev vars (*rev only to make debugging easier and have names match up... not needed *)
      | false -> create_k_ints (k - 1) ((mk_symbol srk ~name:(basename^equiv_num^","^(string_of_int k)) arttype) :: vars) basename equiv_num arttype
    end
  in
  let rec helper alphas equiv_pairs =
    match alphas with
    | [] -> equiv_pairs
    | hd :: tl -> 
      (*Transformers for given equiv class*)
      let kstack = (create_k_ints num_trans [] "K" (string_of_int (List.length alphas)) `TyInt) in
      (*Denotes which transformer a given equiv class was reset on*)
      let rvar = (mk_symbol srk ~name:("R"^(string_of_int (List.length alphas))) `TyInt) in
      (*The sum of transformers for a given equiv class*)
      let kstacksum = (mk_symbol srk ~name:("KSUM"^(string_of_int (List.length alphas))) `TyInt) in 
      (*Starting value for given row of equiv class*)
      let svaralpha = create_k_ints (M.nb_rows hd) [] "S" (string_of_int (List.length alphas)) `TyReal in
      (*One grouping per equiv class*)
      let equiv_pair = (kstack, List.map (fun svar -> let res = (svar, !bdim) in bdim := !bdim + 1; res) svaralpha, rvar, kstacksum) in
      helper tl (equiv_pair :: equiv_pairs)
  in
  helper alphas []

(* Make input terms in list each >= 0 *)
let create_exp_positive_reqs srk kvarst =
  mk_and srk (List.map (fun var -> 
      mk_leq srk (mk_zero srk) var) 
      (List.flatten kvarst))

(* If a coherence class has, after its "final reset",
 * taken the same number of transitions
 * as the loop counter, then that coherence class was never reset. 
 * In this case, its corresponding reset var is set to -1, which
 * means exactly that this coherence class not not reset.
 *)
let exp_full_transitions_reqs srk kvarst rvarst loop_counter =
  mk_and srk  
    (List.map2 
       (fun kvart_stack rvarsti -> 
          mk_iff srk
            (mk_eq srk
               (mk_add srk kvart_stack)
               loop_counter)
            (mk_eq srk rvarsti (mk_real srk (QQ.of_int (-1)))))
       kvarst rvarst)
(* Replacing kvarst with ksums here seems to deoptimize. Unclear why *)

(* Creates list of pairs coherence class vars (for every pair) *)
let all_pairs_kvarst_rvarst ksumst kvarst (rvarst : 'a Syntax.term list) =
  let rec helper1 (sum1, kstack1, r1) ksumst' kvarst' rvarst' =
    begin match ksumst', kvarst', rvarst' with
      | [], [], [] -> []
      | khd :: ktl, ksthd :: ksttl, rhd :: rtl -> 
        (sum1, kstack1, r1, khd, ksthd, rhd) :: (helper1 (sum1, kstack1, r1) ktl ksttl rtl)
      | _ -> assert false
    end
  in
  let rec helper2 ksumst kvarst rvarst =
    match ksumst, kvarst, rvarst with
    | [], [], [] -> []
    | khd :: ktl, ksthd :: ksttl, rhd :: rtl -> (helper1 (khd, ksthd, rhd) ktl ksttl rtl) :: (helper2 ktl ksttl rtl)
    | _ -> assert false
  in
  List.flatten (helper2 ksumst kvarst rvarst)

(* Create every permutation of ordering for coherence classes *)
let exp_perm_constraints srk krpairs =
  mk_and srk
    (List.map 
       (fun (_, k1, _, _, k2, _) -> 
          let lessthan k1 k2 = mk_and srk 
              (List.map2 (fun k1' k2' ->
                   mk_leq srk k1' k2') k1 k2)
          in
          mk_or srk [lessthan k1 k2;  lessthan k2 k1])
       krpairs)

(*If two coherence classes have taken
 * the same number of transitions after their last reset, 
 * both coherence classes must've been reset at same time*)
let exp_equality_k_constraints srk krpairs =
  mk_and srk
    (List.map
       (fun (k1, _, r1, k2, _, r2) ->
          mk_iff srk
            (mk_eq srk
               k1
               k2)
            (mk_eq srk r1 r2))
       krpairs)


(*If ksum equiv pair 1 smaller ksum equiv pair 2, ksum equiv pair 2
 * took path that equiv pair 1 reset on at least once*)
let exp_other_reset srk ksum ksums kvarst trans_num =
  mk_and srk
    (List.mapi (fun ind ksum' ->
         (mk_if srk
            (mk_lt srk
               ksum
               ksum')
            (mk_leq srk
               (mk_one srk)
               (List.nth (List.nth kvarst ind) trans_num))))
        ksums)


(*Either svar for each row in equiv class in x and equiv class not reset or equiv class reset
 * at transformer i and svars equal the reset dim at transformer i*)
let exp_sx_constraints_helper srk ri ksum ksums svarstdims transformers kvarst unialpha tr_symbols =
  let compute_single_svars svart dim  =
    mk_or srk
      ((mk_and srk
          [(mk_eq srk svart (preify srk tr_symbols (Linear.of_linterm srk (M.row dim unialpha))));
           (mk_eq srk ri (mk_real srk (QQ.of_int (-1))))]) ::
       (BatList.mapi 
          (fun ind {a; b} ->
             if ZZ.equal (Z.coeff dim a) ZZ.one 
             then (mk_false srk) (*Are thesee faster to filter out prior to smt query?*) 
             else 
               mk_and srk
                 [(mk_eq srk svart (mk_real srk (V.coeff dim b)));
                  exp_other_reset srk ksum ksums kvarst ind;
                  (mk_eq srk ri (mk_real srk (QQ.of_int ind)))])
          transformers))
  in
  mk_and srk (List.map (fun (svar,dim) -> compute_single_svars svar dim) svarstdims)

(*See helper function for description*)
let exp_sx_constraints srk equiv_pairs transformers kvarst ksums unialpha tr_symbols =
  mk_and srk
    (List.map (fun (kstack, svarstdims, ri, ksum) ->
         exp_sx_constraints_helper srk ri ksum ksums svarstdims transformers kvarst unialpha tr_symbols)
        equiv_pairs)


(*Make x' equal to the sum of start variable plus kvars * increase*)
let exp_lin_term_trans_constraints srk equiv_pairs transformers unialpha =
  mk_and srk
    (List.map (fun (kstack, svarstdims, ri, _) ->
         mk_and srk
           (List.map (fun (svar, dim) ->
                mk_eq srk
                  (Linear.of_linterm srk (M.row dim unialpha))
                  (mk_add srk
                     (svar :: 
                      (BatList.mapi
                         (fun ind {a; b} ->
                            mk_mul srk [(List.nth kstack ind); mk_real srk (V.coeff dim b)])
                         transformers))))
               svarstdims))
        equiv_pairs)

(* If kvar represents a coherence class/transformer pair, (C, T), such that
 * coherence class C is reset on transformer T, then kvar is 0. Recall that
 * the last reset for coherence class C is instead defined by the corresponding
 * "r" var. This function replaces kvars in terms 
 * (that match the just stated property) with 0 *)
let replace_resets_with_zero srk equiv_pairs transformers : ('a Syntax.term list * ('b * Z.dim) list * 'c * 'd) list =
  (List.map (fun (kstack, svarstdims, ri, ksum) ->
       let (svar, dim) = List.hd svarstdims in
       let kstack =
         (BatList.mapi
            (fun ind {a; b} ->
               if ZZ.equal (Z.coeff dim a) ZZ.zero then (mk_zero srk)
               else (List.nth kstack ind))
            transformers)
       in
       kstack,svarstdims, ri, ksum)
      equiv_pairs)

(*A given ksum cannot be larger than loop counter*)
let exp_kstacks_at_most_k srk ksumst loop_counter=
  mk_and srk
    (List.map
       (fun ksum -> mk_leq srk
           ksum
           loop_counter)
       ksumst)

(*Give ksums meaning*)
let exp_kstack_eq_ksums srk equiv_pairs =
  mk_and srk
    (List.map (fun (kstack, _, _, ksum) ->
         mk_eq srk
           (mk_add srk kstack)
           ksum)
        equiv_pairs)

let map_terms srk = List.map (fun (var : Syntax.symbol) -> mk_const srk var)

let exp_base_helper srk tr_symbols loop_counter alphas transformers invars invarmaxk =
  let maxkinvar = if invarmaxk then (mk_leq srk loop_counter (mk_one srk)) else mk_true srk in
  let num_trans = BatList.length transformers in
  let equiv_pairs = create_exp_vars srk alphas num_trans in
  let equiv_pairst = List.map (fun (kstack, svardims, rvar, ksum) ->
      (map_terms srk kstack, List.map (fun (svar, dim) -> (mk_const srk svar), dim) svardims, mk_const srk rvar, mk_const srk ksum)) equiv_pairs in
  let equiv_pairst = replace_resets_with_zero srk equiv_pairst transformers in
  let kvarst, rvarst, ksumst = List.map (fun (kstack, _, _, _) -> kstack) equiv_pairst, List.map (fun (_, _, rvarst, _) -> rvarst) equiv_pairst,
                               List.map (fun (_, _, _, ksumst) -> ksumst) equiv_pairst in
  let pos_constraints = create_exp_positive_reqs srk ([loop_counter] :: kvarst) in
  let full_trans_constraints = exp_full_transitions_reqs srk kvarst rvarst loop_counter in
  let krpairs = all_pairs_kvarst_rvarst ksumst kvarst rvarst in
  let perm_constraints = exp_perm_constraints srk krpairs in
  let reset_together_constraints = exp_equality_k_constraints srk krpairs in
  let kstack_max_constraints = exp_kstacks_at_most_k srk ksumst loop_counter in
  let base_constraints = exp_lin_term_trans_constraints srk equiv_pairst transformers (unify alphas) in
  let kstack_term_reduction = exp_kstack_eq_ksums srk equiv_pairst in
  let invariants = mk_or srk [mk_eq srk loop_counter (mk_zero srk); mk_and srk invars] in
  let form = 
    mk_and srk [pos_constraints; full_trans_constraints; perm_constraints; kstack_max_constraints;
                reset_together_constraints; base_constraints;
                kstack_term_reduction; invariants; maxkinvar] in
  (form, (equiv_pairst, kvarst, ksumst))



let exp srk tr_symbols loop_counter vabs =
  match vabs with
  | {v; alphas; invars; invarmaxk} ->
    if(M.nb_rows (unify alphas) = 0) then mk_true srk else (
      let (form, (equiv_pairst, kvarst, ksumst)) = exp_base_helper srk tr_symbols loop_counter alphas (TSet.to_list v) invars invarmaxk in
      let sx_constraints = exp_sx_constraints srk equiv_pairst (TSet.to_list v) kvarst ksumst (unify alphas) tr_symbols in
      mk_and srk [form; sx_constraints]
    )


(*Move matrix down by first_row rows*)
let push_rows matrix first_row =
  BatEnum.fold 
    (fun matrix (dim', row) ->  M.add_row (dim' + first_row) row matrix) 
    M.zero 
    (M.rowsi matrix)


let coprod_find_images alpha1 alpha2 = 
  let push_counter_1 = ref 0 in
  let s1, s2, alphas =
    List.fold_left (fun (s1, s2, alphas) alphalist1 -> 
        let push_counter_2 = ref 0 in
        let s1', s2', alpha' = 
          (List.fold_left (fun (s1', s2', alpha') alphalist2 ->
               (*Add offset to rows so that c and d are correct with regards to unified alpha*)
               let alphalist1, alphalist2 = (push_rows alphalist1 !push_counter_1, push_rows alphalist2 !push_counter_2) in
               let (c, d) = Linear.intersect_rowspace alphalist1 alphalist2 in
               push_counter_2 := (M.nb_rows alphalist2) + !push_counter_2;
               (*If c = 0, then intersection of equiv class alphalist1 and alphalist2 form empty equivalence class*)
               if M.equal c M.zero then (s1', s2', alpha') else (c :: s1', d :: s2', (M.mul c alphalist1) :: alpha'))
              ([], [], []) alpha2) in
        push_counter_1 := (M.nb_rows alphalist1) + !push_counter_1; 
        List.append s1' s1, List.append s2' s2, List.append alpha' alphas)
      ([], [], []) alpha1
  in
  s1, s2, alphas

let coprod_use_image v s  =
  (*Computes a rep dimension from equivalence class for each row in morphism*)
  let get_morphism_row_reps unified_morphism = 
    BatEnum.map (fun (dim', row) ->
        match BatEnum.get (V.enum row) with
        | None -> assert false
        | Some (scalar, dim) -> dim
      )
      (M.rowsi (unified_morphism))
  in

  let sreps = BatList.of_enum (get_morphism_row_reps (unify s)) in

  let transformer_image (t : transformer) unified_morphism rowsreps : transformer =
    let a, b = t.a, t.b in
    let b' = M.vector_right_mul (unified_morphism) b in
    let a' = BatEnum.foldi (fun ind dim vector ->
        Z.add_term (Z.coeff dim a) ind vector
      )
        Z.zero
        rowsreps
    in
    {a=a'; b=b'}
  in
  let v' = TSet.fold (fun ele acc -> 
      TSet.add (transformer_image ele (unify s) (BatList.enum sreps)) acc) v TSet.empty in
  v'


 
let coproduct srk vabs1 vabs2 : 'a t =
  let (alpha1, alpha2, v1, v2) = (vabs1.alphas, vabs2.alphas, vabs1.v, vabs2.v) in 
  let s1, s2, alphas = coprod_find_images alpha1 alpha2 in
  let v = TSet.union (coprod_use_image v1 s1) (coprod_use_image v2 s2) in
  {v; alphas;invars=[];invarmaxk=false}


(*List of terms in alpha, preified and postified*)
let term_list srk alphas tr_symbols = 
  List.map (fun matrix -> 
      ((M.rowsi matrix)
       /@ (fun (_, row) -> 
           let term = Linear.of_linterm srk row in
           (preify srk tr_symbols term, term)))
      |> BatList.of_enum)
    alphas
  |> List.flatten

(*Gamma of single transformer*)
let gamma_transformer srk term_list t =
  BatList.mapi (fun ind (pre_term, post_term) -> 
      mk_eq srk 
        post_term 
        (mk_add srk [(mk_mul srk [pre_term; mk_real srk (QQ.of_zz (Z.coeff ind t.a))]);
                     mk_real srk (V.coeff ind t.b)]))
    term_list
  |> mk_and srk


let gamma srk vas tr_symbols : 'a formula =
  match vas with
  | {v; alphas} ->
    let term_list = term_list srk alphas tr_symbols in
    if List.length term_list = 0 then mk_true srk else
      mk_or srk (List.map (fun t -> gamma_transformer srk term_list t) (TSet.elements v))

(*Maybe uncomment for future test cases*)
(*let remove_row vas x y =
  begin match vas with
    | {v; alphas} ->
      let v =
        TSet.fold (fun ele acc ->
            let {a; b} = ele in
            let (_,a) = Z.pivot x a in
            let (_,b) = V.pivot x b in
            let a = Z.add_term (Z.coeff y a) x a in
            let b = V.add_term (V.coeff y b) x b in
            TSet.add ({a;b}) acc) v TSet.empty in
      let (a1, a2) = BatList.split_at (x - 1) alphas in
      (*begin match a2 with
        | hd :: tl ->
        let alphas = a1 @ a2 in
        Vas {v; alphas}
              | [] -> 
              let alphas = a1 in
              Vas {v; alphas}
              end*)
      {v;alphas;invars=[];invarmaxk=false}
  end
*)



let matrixify_vectorize_term_list srk vl = 
  let add_dim m b term =
    let (b', v) = V.pivot (Linear.const_dim) (Linear.linterm_of srk term) in
    M.add_row (M.nb_rows m) v m, V.add_term (QQ.negate b') (M.nb_rows m) b
  in
  List.fold_left (fun (m, b) ele -> add_dim m b ele) (M.zero, V.zero) vl

let combine_affine_hulls srk aff1 aff2 a1 a2 =   
  let add_dim m b a term a' offset =
    let (b', v) = V.pivot (Linear.const_dim) (Linear.linterm_of srk term) in
    (M.add_row (M.nb_rows m) v m, V.add_term (QQ.negate b') (offset + (M.nb_rows m)) b, Z.add_term a' (offset + (M.nb_rows m)) a)
  in
  let f a' offset = List.fold_left (fun (m, b, a) ele -> add_dim m b a ele a' offset) in
  let (m1,b,a) = f a1 0 (M.zero, V.zero, Z.zero) aff1 in
  let (m2, b, a) = f a2 (M.nb_rows m1) (M.zero, b, a) aff2 in
  match M.equal m1 (M.zero), M.equal m2 (M.zero) with
  | true, true -> mk_top
  | false, true -> {v=TSet.singleton {a;b}; alphas=[m1];invars=[];invarmaxk=false}
  | true, false ->  {v=TSet.singleton {a;b}; alphas=[m2];invars=[];invarmaxk=false} 
  | false, false -> {v=TSet.singleton {a;b}; alphas=[m1;m2];invars=[];invarmaxk=false}

let alpha_hat srk imp tr_symbols xdeltpairs xdeltphis =
  let postify' = postify srk xdeltpairs in 
  let r = H.affine_hull srk imp (List.map (fun (x, x') -> x') tr_symbols) in
  let i' = H.affine_hull srk (mk_and srk (imp :: xdeltphis)) (List.map (fun (x'', x') -> x'') xdeltpairs) in
  let i = List.map postify' i' in
  combine_affine_hulls srk i r ZZ.one ZZ.zero

let find_invariants  (srk : 'a context) (symbols : (symbol * symbol) list) (body : 'a formula) =
  (* Find rightmost dimension of vector, and coeff of that dim *)
  let get_last_dim vector =
    BatEnum.fold (fun (scal, max) (scalar, dim) ->
        if dim > max then (scalar,dim) else (scal, max)) (QQ.zero, -1) (V.enum vector) in
  (* Compute when constant relations on post state vars; on pre state vars *)
  let post = H.affine_hull srk body (List.map (fun (x, x') -> x') symbols) in
  let pre = H.affine_hull srk body (List.map (fun (x, x') -> x) symbols) in
  (* Convert pre-state vars to post-states vars; for rowspace intersection *)
  let pre' = List.map (postify srk symbols) pre in
  (* Matrixify thr affine hulls *)
  match combine_affine_hulls srk post pre' ZZ.zero ZZ.zero with
  | {v;alphas=[]} -> (body, [], false)
  | {v;alphas=[hd]} -> (body, [], false)
  | {v;alphas=[up;pr]} ->
    let b = (List.hd (TSet.elements v)).b in
    let (c, d) = Linear.intersect_rowspace up pr in
    (* The intersection of c and d tells us which invariants hold
     * at every step of the loop *)
    BatEnum.fold (fun (body', invars, invarmaxk) (dim', crow) ->
        let vect = M.vector_left_mul crow up in
        let b_post = V.dot crow b in 
        let prerow = M.row dim' d in
        (* Shifting rows to account for offset in b *)
        let prerow' = 
          BatEnum.fold (fun row_acc (ele, rdim) ->
              V.add_term ele (rdim + (M.nb_rows up)) row_acc) V.zero (V.enum prerow) in
        let br = V.dot prerow' b in

        let scal, last_dim = get_last_dim vect in
        let term_xy' =  
            (mk_mul srk 
               [mk_sub srk (Linear.of_linterm srk (snd (V.pivot last_dim vect))) 
                  (mk_real srk br);
                mk_real srk (QQ.inverse (QQ.negate scal))]) in
        let term_xy = preify srk symbols
            (mk_mul srk 
               [mk_sub srk (Linear.of_linterm srk (snd (V.pivot last_dim vect))) 
                  (mk_real srk b_post);
                mk_real srk (QQ.inverse (QQ.negate scal))]) in

        let sym' = match Linear.sym_of_dim last_dim with
          | None -> assert false
          | Some v -> v
        in
        let sym = List.fold_left (fun acc (x, x') -> if x' = sym' then x else acc) sym' symbols in
        let body' = substitute_const srk (fun x -> if x = sym then preify srk symbols term_xy 
                                           else if x = sym' then postify srk symbols term_xy'
                                           else mk_const srk x) body' in
        let invars = (mk_eq srk (mk_const srk sym') (term_xy')) :: (mk_eq srk (mk_const srk sym) (term_xy)) :: invars in
        let invarmaxk' = if QQ.equal b_post br then invarmaxk else true in 
        body',invars, invarmaxk'
      )
      (body,[], false)
      (M.rowsi c)
  | _ -> assert false


let ident_matrix_syms srk symbols =
  BatList.fold_lefti (fun matr dim (x, x') ->
      M.add_row dim (Linear.linterm_of srk (mk_const srk x')) matr) M.zero symbols

let ident_matrix_real n =
  BatList.fold_left (fun matr dim  ->
      M.add_entry dim dim (QQ.of_int 1) matr) M.zero (BatList.of_enum (0--n))

let mk_bottom srk symbols =
  {v=TSet.empty; alphas=[ident_matrix_syms srk symbols];invars=[];invarmaxk=false}

(*Make a better pp function... need invars and maxk*)
let pp srk syms formatter vas = Format.fprintf formatter "%a" (Formula.pp srk) (gamma srk vas syms)

let abstract ?(exists=fun x -> true) srk tr_symbols phi  =
  let phi = (rewrite srk ~down:(nnf_rewriter srk) phi) in
  let phi = Nonlinear.linearize srk phi in
  let (xdeltpairs, xdelta_formula) = 
    List.split (List.fold_left (fun acc (x, x') -> 
        let xdelta = (mk_symbol srk (typ_symbol srk x)) in
        let xdelta_formula = (mk_eq srk (mk_const srk xdelta) 
                          (mk_sub srk (mk_const srk x') (mk_const srk x))) in
        ((xdelta, x'), xdelta_formula) :: acc) [] tr_symbols) in
  let phi,cinvars, invarmaxk = find_invariants srk tr_symbols phi in
  let solver = Smt.mk_solver srk in
  let rec go vas =
    Smt.Solver.add solver [mk_not srk (gamma srk vas tr_symbols)];
    match Smt.Solver.get_model solver with
    | `Unsat -> vas
    | `Unknown -> assert false
    | `Sat m ->
      match Interpretation.select_implicant m phi with
      | None -> assert false
      | Some imp ->
        let sing_transformer_vas = alpha_hat srk (mk_and srk imp) tr_symbols xdeltpairs xdelta_formula in
        go (coproduct srk vas sing_transformer_vas)
  in
  Smt.Solver.add solver [phi];
  let {v;alphas;_} = go (mk_bottom srk tr_symbols) in
  let result = {v;alphas;invars=cinvars;invarmaxk} in
  result



let join  (srk :'a context) (tr_symbols : (symbol * symbol) list) (vabs1 : 'a t) (vabs2 : 'a t) = assert false
let widen  (srk :'a context) (tr_symbols : (symbol * symbol) list) (vabs1 : 'a t) (vabs2 : 'a t) = assert false
let equal (srk : 'a context) (tr_symbols : (symbol * symbol) list) (vabs1 : 'a t) (vabs2 : 'a t) = assert false

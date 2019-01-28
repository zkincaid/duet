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
include Log.Make(struct let name = "srk.mdvas" end)

type transformer =
  { a : Z.t;
    b : V.t }
[@@deriving ord, show]

module Transformer = struct
  type t = transformer
  [@@deriving ord, show]
end

module TSet = BatSet.Make(Transformer)

type vas = TSet.t

let pp_vas formatter (vas : vas) : unit =
  SrkUtil.pp_print_enum pp_transformer formatter (TSet.enum vas)  

type 'a t = { v : vas; alphas : M.t list; invars : 'a formula list; invarmaxk : bool}

let mk_top = {v=TSet.empty; alphas=[]; invars=[]; invarmaxk=false}

(*Vertically stack matrices*)
let unify (alphas : M.t list) : M.t =
  let unified = List.fold_left (fun matrix alphacell -> 
      BatEnum.fold (fun matrix (dim, vector) ->
          M.add_row (M.nb_rows matrix) vector matrix) 
        matrix 
        (M.rowsi alphacell))
      M.zero alphas in
  unified 


let post_map srk tr_symbols =
  List.fold_left
    (fun map (sym, sym') -> Symbol.Map.add sym (mk_const srk sym') map)
    Symbol.Map.empty
    tr_symbols

let preify srk tr_symbols = substitute_map srk (post_map srk (List.map (fun (x, x') -> (x', x)) tr_symbols))
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

(*Make input terms in list each >= 0*)
let create_exp_positive_reqs srk kvarst =
  mk_and srk (List.map (fun var -> 
      mk_leq srk (mk_zero srk) var) 
      (List.flatten kvarst))

(*If a kstack is full, then that equiv class never reset*)
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

(*Create every pairing of (ksum, kstack, reset var) for each equiv class*)
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

(*Create every permutation of ordering for equiv classes*)
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

(*If two pairings have equal sums, must've been reset at same time*)
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

(*Replace terms in kvar with 0 when kvar matches to a reset for respective equiv class*)
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


let alpha_hat (srk : 'a context) (imp : 'a formula) symbols x''s  x''_forms doubleres  = 
  let postify' = postify srk x''s in 
  let r = H.affine_hull srk imp (List.map (fun (x, x') -> x') symbols) in
  let i' = H.affine_hull srk (mk_and srk (imp :: x''_forms)) (List.map (fun (x'', x') -> x'') x''s) in
  let i = List.map postify' i' in
  (*Adds dim to m b a; offset to account for stacking of inc and res in transformer*)
  let add_dim m b a term a' offset =
    let (b', v) = V.pivot (Linear.const_dim) (Linear.linterm_of srk term) in
    (M.add_row (M.nb_rows m) v m, V.add_term (QQ.negate b') (offset + (M.nb_rows m)) b, Z.add_term a' (offset + (M.nb_rows m)) a)
  in
  let f t offset = List.fold_left (fun (m, b, a) ele -> add_dim m b a ele t offset) in
  let (mi,b,a) = f (if doubleres then ZZ.zero else ZZ.one) 0 (M.zero, V.zero, Z.zero) i in
  let (mr, b, a) = f ZZ.zero (M.nb_rows mi) (M.zero, b, a) r in
  match M.equal mi (M.zero), M.equal mr (M.zero) with
  | true, true -> mk_top
  | false, true -> {v=TSet.singleton {a;b}; alphas=[mi];invars=[];invarmaxk=false}
  | true, false ->  {v=TSet.singleton {a;b}; alphas=[mr];invars=[];invarmaxk=false} 
  | false, false -> {v=TSet.singleton {a;b}; alphas=[mi;mr];invars=[];invarmaxk=false}



let find_invariants  (srk : 'a context) (symbols : (symbol * symbol) list) (body : 'a formula) =
  let get_last_dim vector =
    BatEnum.fold (fun (scal, high) (scalar, dim) ->
        if dim > high then (scalar,dim) else (scal, high)) (QQ.zero, -1) (V.enum vector) in
  match alpha_hat srk body symbols symbols [] true with
  | {v;alphas=[]} -> (body, [], false)
  | {v;alphas=[hd]} -> (body, [], false)
  | {v;alphas=[up;pr]} ->
    let {a;b} = List.hd (TSet.elements v) in
    let (c, d) = Linear.intersect_rowspace up pr in
    BatEnum.fold (fun (body', invars, invarmaxk) (dim', crow) ->
        let vect = M.vector_left_mul crow up in
        let bi = V.dot crow b in 
        let rrow = M.row dim' d in
        let rrow' = 
          BatEnum.fold (fun row_acc (ele, rdim) ->
              V.add_term ele (rdim + (M.nb_rows up)) row_acc) V.zero (V.enum rrow) in
        let br = V.dot rrow' b in

        let scal, last_dim = get_last_dim vect in
        let term_xy' =  
            (mk_mul srk 
               [mk_sub srk (Linear.of_linterm srk (snd (V.pivot last_dim vect))) 
                  (mk_real srk br);
                mk_real srk (QQ.inverse (QQ.negate scal))]) in
        let term_xy = preify srk symbols
            (mk_mul srk 
               [mk_sub srk (Linear.of_linterm srk (snd (V.pivot last_dim vect))) 
                  (mk_real srk bi);
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
        let invarmaxk' = if QQ.equal bi br then invarmaxk else true in 
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

let abstract ?(exists=fun x -> true) (srk : 'a context) (symbols : (symbol * symbol) list) (body : 'a formula)  =
  let body = (rewrite srk ~down:(nnf_rewriter srk) body) in
  let body = Nonlinear.linearize srk body in
  let (x''s, x''_forms) = 
    List.split (List.fold_left (fun acc (x, x') -> 
        let x'' = (mk_symbol srk (typ_symbol srk x)) in
        let x''_form = (mk_eq srk (mk_const srk x'') 
                          (mk_sub srk (mk_const srk x') (mk_const srk x))) in
        ((x'', x'), x''_form) :: acc) [] symbols) in
  let solver = Smt.mk_solver srk in
  let body,cinvars, invarmaxk = find_invariants srk symbols body in
  let rec go vas count =
    assert (count > 0);
    Smt.Solver.add solver [mk_not srk (gamma srk vas symbols)];
    match Smt.Solver.get_model solver with
    | `Unsat -> vas
    | `Unknown -> assert false
    | `Sat m ->
      match Interpretation.select_implicant m body with
      | None -> assert false
      | Some imp ->
        Log.errorf "INTERMEDIATE VAS: %a"  (Formula.pp srk) (gamma srk vas symbols); 
        let alpha_v = alpha_hat srk (mk_and srk imp) symbols x''s x''_forms false in
        go (coproduct srk vas alpha_v) (count - 1)
  in
  Smt.Solver.add solver [body];
  let {v;alphas;_} = go (mk_bottom srk symbols) 20 in
  let result = {v;alphas;invars=cinvars;invarmaxk} in
  Log.errorf "Final VAS: %a"  (Formula.pp srk) (gamma srk result symbols);
  result



let join  (srk :'a context) (tr_symbols : (symbol * symbol) list) (vabs1 : 'a t) (vabs2 : 'a t) = assert false
let widen  (srk :'a context) (tr_symbols : (symbol * symbol) list) (vabs1 : 'a t) (vabs2 : 'a t) = assert false
let equal (srk : 'a context) (tr_symbols : (symbol * symbol) list) (vabs1 : 'a t) (vabs2 : 'a t) = assert false

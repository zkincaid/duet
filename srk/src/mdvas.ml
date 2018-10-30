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
(* Consider changing a to bool vector *)

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
      | false -> create_k_ints (k - 1) ((mk_symbol srk ~name:(basename^equiv_num^"COM"^(string_of_int k)) arttype) :: vars) basename equiv_num arttype
    end
  in
  let rec helper alphas kvars svars rvars equiv_pairs ksums =
    match alphas with
    | [] -> kvars, svars, rvars, equiv_pairs, ksums
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
      helper tl (kstack :: kvars) (svaralpha :: svars) (rvar :: rvars) (equiv_pair :: equiv_pairs) (kstacksum :: ksums)
  in
  helper alphas [] [] [] [] []

(*Make passed in variables each be >= 0*)
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
    | khd :: khdd :: ktl, ksthd :: ksthdd :: ksttl, rhd :: rhdd :: rtl ->
      (helper1 (khd, ksthd, rhd) (khdd :: ktl) (ksthdd :: ksttl) (rhdd :: rtl)) :: (helper2 (khdd :: ktl) (ksthdd :: ksttl) (rhdd :: rtl))
    | khd :: ktl, ksthd :: ksttl, rhd :: rtl -> []
    | _ -> assert false
  in
  List.flatten (helper2 ksumst kvarst rvarst)

(*Create every permutation of ordering for equiv classes*)
let exp_perm_constraints srk krpairs =
  mk_and srk
    (List.map 
       (fun (_, k1, r1, _, k2, r2) -> 
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
          [(mk_eq srk svart (preify srk tr_symbols (Linear.of_linterm srk (M.row dim unialpha)))); (*pivot or row? need to make sure alpha and dim both indexed same *)
           (mk_eq srk ri (mk_real srk (QQ.of_int (-1))))]) ::
       (BatList.mapi 
          (fun ind {a; b} ->
             if ZZ.equal (Z.coeff dim a) ZZ.one 
             then (mk_false srk)
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
         mk_and srk (* the lack of or worries me a bit here *)
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

(*If a kvar in a kstack is a reset for given equiv class, this kvar must be 0*)
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


let exp_base_helper srk tr_symbols loop_counter alphas transformers invars invarmaxk vas_only =
  let maxkinvar = if invarmaxk then (mk_leq srk loop_counter (mk_one srk)) else mk_true srk in
  let num_trans = BatList.length transformers in
  let kvars, svars, rvars, equiv_pairs, ksums = create_exp_vars srk alphas num_trans in
  let svars = List.flatten svars in
  let kvarst : 'a Syntax.term list list  = List.map (fun listvars -> map_terms srk listvars) kvars in
  let svarst, rvarst, ksumst  = map_terms srk svars, map_terms srk rvars, map_terms srk ksums in
  let equiv_pairst = List.map (fun (kstack, svardims, rvar, ksum) ->
      (map_terms srk kstack, List.map (fun (svar, dim) -> (mk_const srk svar), dim) svardims, mk_const srk rvar, mk_const srk ksum)) equiv_pairs in
  let equiv_pairst = replace_resets_with_zero srk equiv_pairst transformers in
  let kvarst = List.map (fun (kstack, _, _, _) -> kstack) equiv_pairst in
  let pos_constraints = create_exp_positive_reqs srk ([loop_counter] :: kvarst) in
  let full_trans_constraints = exp_full_transitions_reqs srk kvarst rvarst loop_counter in
  let krpairs = all_pairs_kvarst_rvarst ksumst kvarst rvarst in
  let perm_constraints = exp_perm_constraints srk krpairs in
  let reset_together_constraints = exp_equality_k_constraints srk krpairs in
  let kstack_max_constraints = exp_kstacks_at_most_k srk ksumst loop_counter in
  let base_constraints = exp_lin_term_trans_constraints srk equiv_pairst transformers (unify alphas) in
  let kstack_term_reduction = exp_kstack_eq_ksums srk equiv_pairst in
  let invariants = mk_or srk [mk_eq srk loop_counter (mk_zero srk); mk_and srk invars] in
  let sx_constraints = if(vas_only) then exp_sx_constraints srk equiv_pairst transformers kvarst ksumst (unify alphas) tr_symbols 
    else mk_true srk in
  let form = 
    mk_and srk [pos_constraints; full_trans_constraints; perm_constraints; kstack_max_constraints;
                reset_together_constraints; sx_constraints; base_constraints;
                kstack_term_reduction; invariants; maxkinvar] in
  (form, (equiv_pairst, kvarst, svarst, rvarst, ksumst))



let exp srk tr_symbols loop_counter vabs =
  match vabs with
  | {v; alphas; invars; invarmaxk} ->
    if(M.nb_rows (unify alphas) = 0) then mk_true srk else (
      let (form, _) = exp_base_helper srk tr_symbols loop_counter alphas (TSet.to_list v) invars invarmaxk true in
      form
    )


let push_rows matrix first_row =
  BatEnum.fold 
    (fun matrix (dim', row) ->  M.add_row (dim' + first_row) row matrix) 
    M.zero 
    (M.rowsi matrix)

let coproduct srk vabs1 vabs2 : 'a t =
  match vabs1, vabs2 with
  | vabs1, vabs2 ->
    let (v1, v2, alpha1, alpha2) = (vabs1.v, vabs2.v, vabs1.alphas, vabs2.alphas) in
    let push_counter_1 = ref 0 in
    Log.errorf "In the right place";
    let s1, s2, alphas =
      List.fold_left (fun (s1, s2, alphas) alphalist1 -> 
          let push_counter_2 = ref 0 in
          let s1', s2', alpha' = 
            (List.fold_left (fun (s1', s2', alpha') alphalist2 ->
                 let alphalist1, alphalist2 = (push_rows alphalist1 !push_counter_1, push_rows alphalist2 !push_counter_2) in
                 let (c, d) = Linear.intersect_rowspace alphalist1 alphalist2 in
                 push_counter_2 := (M.nb_rows alphalist2) + !push_counter_2; (* THIS IS EXTREMELY UNSAFE.... it requires every row of a given alpha list to start at 0 and have no gaps *)
                 if M.equal c M.zero then (s1', s2', alpha') else (c :: s1', d :: s2', (M.mul c alphalist1) :: alpha'))
                ([], [], []) alpha2) in
          push_counter_1 := (M.nb_rows alphalist1) + !push_counter_1; 
          List.append s1' s1, List.append s2' s2, List.append alpha' alphas)
        ([], [], []) alpha1
    in


    let transformer_image (t : transformer) unified_morphism test : transformer =
      let a, b = t.a, t.b in
      let b' = M.vector_right_mul (unified_morphism) b in
      let a' = BatEnum.fold (fun vector (dim', row) ->
          let dim = match BatEnum.get (V.enum row) with
            | None -> assert false
            | Some (scalar, dim) -> dim
          in
          Z.add_term 
            (Z.coeff dim a)
            dim'
            vector
        )
          Z.zero
          (M.rowsi (unified_morphism)) (* Make a function that just computes all unified reps once *)
      in
      {a=a'; b=b'}
    in
    let ti_fun vas uni_m test = TSet.fold (fun ele acc -> 
        TSet.add (transformer_image ele uni_m test) acc) vas TSet.empty in
    let v = TSet.union (ti_fun v1 (unify s1) true) (ti_fun v2 (unify s2) false) in (* Should just put top if no transformers, bottom if conflicting *)
    {v; alphas;invars=[];invarmaxk=false}



let term_list srk alphas tr_symbols = 
  List.map (fun matrix -> 
      ((M.rowsi matrix)
       /@ (fun (_, row) -> 
           let term = Linear.of_linterm srk row in
           (preify srk tr_symbols term, term)))
      |> BatList.of_enum)
    alphas
  |> List.flatten

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

(*Very unsafe*)
let remove_row vas x y =
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



let alpha_hat (srk : 'a context) (imp : 'a formula) symbols x''s  x''_forms othersyms = 
  let postify = substitute_map srk (post_map srk x''s) in 
  let r = H.affine_hull srk imp ((List.map (fun (x, x') -> x') symbols) @ othersyms) in
  let i' = H.affine_hull srk (mk_and srk (imp :: x''_forms)) ((List.map (fun (x'', x') -> x'') x''s) @ othersyms) in
  let i = List.map postify i' in
  let add_dim m b a term a' offset =
    let (b', v) = V.pivot (Linear.const_dim) (Linear.linterm_of srk term) in
    (M.add_row ((*offset +*) (M.nb_rows m)) v m, V.add_term (QQ.negate b') (offset + (M.nb_rows m)) b, Z.add_term a' (offset + (M.nb_rows m)) a)
  in
  let f t offset = List.fold_left (fun (m, b, a) ele -> add_dim m b a ele t offset) in
  let (mi,b,a) = f ZZ.one 0 (M.zero, V.zero, Z.zero) i in
  let (mr, b, a) = f ZZ.zero (M.nb_rows mi) (M.zero, b, a) r in
  match M.equal mi (M.zero), M.equal mr (M.zero) with
  | true, true -> mk_top
  | false, true -> {v=TSet.singleton {a;b}; alphas=[mi];invars=[];invarmaxk=false}
  | true, false ->  {v=TSet.singleton {a;b}; alphas=[mr];invars=[];invarmaxk=false} 
  | false, false -> {v=TSet.singleton {a;b}; alphas=[mi;mr];invars=[];invarmaxk=false} (* Matrix 1 row 1 maps to first element a, first elemebt b *)






let find_invariants  (srk : 'a context) (symbols : (symbol * symbol) list) (body : 'a formula) =
  let postify = substitute_map srk (post_map srk symbols) in
  let (x''s, x''_forms) = 
    List.split (List.fold_left (fun acc (x, x') -> 
        let x'' = (mk_symbol srk `TyReal) in
        let x''_form = (mk_eq srk (mk_const srk x'') 
                          (mk_sub srk (mk_const srk x') (mk_const srk x))) in
        ((x'', x'), x''_form) :: acc) [] symbols) in
  let get_last_dim vector =
    BatEnum.fold (fun (scal, high) (scalar, dim) ->
        if dim > high then (scalar,dim) else (scal, high)) (QQ.zero, -1) (V.enum vector) in
  match alpha_hat srk body symbols x''s x''_forms [] with
  | {v;alphas=[]} -> (body, [], false)
  | {v;alphas=[hd]} -> Log.errorf "THERE WERE NO INVARIANTS FOUND"; (body, [], false)
  | {v;alphas=[mi;mr]} ->
    Log.errorf "THE INVARIANT VAS IS: %a"  (Formula.pp srk) (gamma srk {v;alphas=[mi;mr];invars=[];invarmaxk=false} symbols);
    let {a;b} = List.hd (TSet.elements v) in
    let (c, d) = Linear.intersect_rowspace mi mr in
    BatEnum.fold (fun (body', invars, invarmaxk) (dim', crow) ->
        let vect = M.vector_left_mul crow mi in
        let bi = V.dot crow b in 
        let invarmaxk' = if QQ.equal bi (QQ.zero) then invarmaxk else true in
        let rrow = M.row dim' d in
        let rrow' = 
          BatEnum.fold (fun row_acc (ele, rdim) ->
              V.add_term ele (rdim + (M.nb_rows mi)) row_acc) V.zero (V.enum rrow) in
        let br = V.dot rrow' b in


        let scal, last_dim = get_last_dim vect in
        let term_xy' = postify  
            (mk_mul srk 
               [mk_sub srk (Linear.of_linterm srk (snd (V.pivot last_dim vect))) 
                  (mk_real srk br);
                mk_real srk (QQ.inverse (QQ.negate scal))]) in
        Log.errorf "New terk %a" (Term.pp srk) term_xy'; 
        let term_xy = preify srk symbols
            (mk_mul srk
               [mk_add srk 
                  [mk_sub srk (Linear.of_linterm srk (snd (V.pivot last_dim vect)))
                     (mk_real srk br);
                   mk_real srk  bi];
                mk_real srk (QQ.inverse (QQ.negate scal))]) in
        let sym = match Linear.sym_of_dim last_dim with
          | None -> assert false
          | Some v -> v
        in
        let sym' = List.fold_left (fun acc (x, x') -> if x = sym then x' else acc) sym symbols in
        let sym = List.fold_left (fun acc (x, x') -> if x' = sym' then x else acc) sym' symbols in
        Log.errorf "SYMBOL IS %a" (Formula.pp srk) (mk_const srk sym);
        Log.errorf "SYMBOL IS %a" (Formula.pp srk) (mk_const srk sym');
        let body' = substitute_const srk (fun x -> if x = sym then preify srk symbols term_xy 
                                           else if x = sym' then postify term_xy'
                                           else mk_const srk x) body' in
        Log.errorf "New body %a" (Formula.pp srk) body';
        let invars = (mk_eq srk (mk_const srk sym') (term_xy')) :: (mk_eq srk (mk_const srk sym) (term_xy)) :: invars in
        List.fold_left (fun _ invar -> Log.errorf "Invars is %a" (Formula.pp srk) invar;())() invars;
        body',invars, invarmaxk'
      )
      (body,[], false)
      (M.rowsi c)
  | _ -> assert false


let ident_matrix srk symbols =
  BatList.fold_lefti (fun matr dim (x, x') ->
      M.add_row dim (Linear.linterm_of srk (mk_const srk x')) matr) M.zero symbols


let mk_bottom srk symbols =
  Log.errorf "Matrix is %a" (M.pp) (ident_matrix srk symbols);
  {v=TSet.empty; alphas=[ident_matrix srk symbols];invars=[];invarmaxk=false}


let pp srk syms formatter vas = Format.fprintf formatter "%a" (Formula.pp srk) (gamma srk vas syms)

let abstract ?(exists=fun x -> true) (srk : 'a context) (symbols : (symbol * symbol) list) (body : 'a formula)  =
  let allsym = List.fold_left (fun acc (x, x') -> x :: x' :: acc) [] symbols in
  let othersyms = Syntax.Symbol.Set.fold (fun sym acc -> if List.mem sym allsym then acc else sym :: acc) (Syntax.symbols body) [] in
  Syntax.Symbol.Set.iter (fun s -> Log.errorf "Symbol is %a %B" (pp_symbol srk) s (exists s)) (Syntax.symbols body);
  let othersyms = [] in
  let body = (rewrite srk ~down:(nnf_rewriter srk) body) in
  let body = Nonlinear.linearize srk body in
  let (x''s, x''_forms) = 
    List.split (List.fold_left (fun acc (x, x') -> 
        let x'' = (mk_symbol srk `TyReal) in
        let x''_form = (mk_eq srk (mk_const srk x'') 
                          (mk_sub srk (mk_const srk x') (mk_const srk x))) in
        ((x'', x'), x''_form) :: acc) [] symbols) in
  let postify = substitute_map srk (post_map srk x''s) in
  let solver = Smt.mk_solver srk in
  let body,cinvars, invarmaxk = find_invariants srk symbols body in
  BatList.iter (fun invar -> Log.errorf "One invar is %a" (Formula.pp srk) invar) cinvars;
  Log.errorf "The new formula is %a" (Formula.pp srk) body;
  Log.errorf "Here";
  let rec go vas count =
    assert (count > 0);
    (*Log.errorf "Current VAS: %a" (Formula.pp srk) (gamma srk vas symbols);
      Log.errorf "___________________________";*)
    Smt.Solver.add solver [mk_not srk (gamma srk vas symbols)];
    match Smt.Solver.get_model solver with
    | `Unsat -> vas
    | `Unknown -> assert false
    | `Sat m ->
      match Interpretation.select_implicant m body with
      | None -> assert false
      | Some imp ->
        let alpha_v = alpha_hat srk (mk_and srk imp) symbols x''s x''_forms othersyms in
        (*if alpha_v = Top then Top else*)
        Log.errorf "Inter VAS: %a"  (Formula.pp srk) (gamma srk (coproduct srk vas alpha_v) symbols);

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



module Mdvass = struct
  module Int = SrkUtil.Int


  type 'a t = { label : ('a formula) array;
                graph : vas array array;
                simulation : M.t list;
                invars : 'a formula list;
                invarmaxk : bool
              }



  let pp _ _ = assert false


  let join  (srk :'a context) (tr_symbols : (symbol * symbol) list) (vabs1 : 'a t) (vabs2 : 'a t) = assert false
  let widen  (srk :'a context) (tr_symbols : (symbol * symbol) list) (vabs1 : 'a t) (vabs2 : 'a t) = assert false
  let equal (srk : 'a context) (tr_symbols : (symbol * symbol) list) (vabs1 : 'a t) (vabs2 : 'a t) = assert false


  let compute_transformers_two_nodes srk l1 l2 transformers term_list tr_symbols formula =
    let solver = Smt.mk_solver srk in
    TSet.filter (fun trans ->
        Smt.Solver.reset solver;
        let trans_constraint = gamma_transformer srk term_list trans in
        let form = (rewrite srk ~down:(nnf_rewriter srk) (mk_and srk [l1; trans_constraint; postify srk tr_symbols l2; formula])) in 

        Smt.Solver.add solver [form];
        match Smt.Solver.get_model solver with
        | `Unsat -> false
        | `Unknown -> true
        | `Sat _ -> true
      ) transformers



  let compute_edges srk transformers tr_symbols alphas label formula =
    let term_list = term_list srk alphas tr_symbols in 
    let graph = Array.make_matrix (Array.length label) (Array.length label) (TSet.empty) in
    BatArray.iteri (fun ind1 arr -> 
        BatArray.modifyi (fun ind2 _ ->
            compute_transformers_two_nodes srk label.(ind1) label.(ind2) transformers term_list tr_symbols formula)
          arr) 
      graph;
    graph

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

  let get_pre_with_post_labels srk formula exists tr_symbols =
    let pre_symbols = pre_symbols tr_symbols in
    let post_symbols = post_symbols tr_symbols in
    let solver = Smt.mk_solver srk in
    let man = Polka.manager_alloc_strict () in
    let exists_pre x =
      exists x && not (Symbol.Set.mem x post_symbols)
    in
    let exists_post x =
      exists x && not (Symbol.Set.mem x pre_symbols)
    in
    let rec find_prepost labels = 
      match Smt.Solver.get_model solver with
      | `Unsat -> labels
      | `Unknown -> assert false
      | `Sat m ->
        match Interpretation.select_implicant m formula with
        | None -> assert false
        | Some imp ->
          let pre_imp = SrkApron.formula_of_property (Abstract.abstract ~exists:exists_pre srk man (mk_and srk imp)) in
          let post_imp = SrkApron.formula_of_property (Abstract.abstract ~exists:exists_post srk man (mk_and srk imp)) in
          Smt.Solver.add solver [mk_not srk pre_imp];
          find_prepost ((pre_imp, post_imp) :: labels)
    in
    Smt.Solver.reset solver;
    Smt.Solver.add solver [formula];
    let prepost_labels = List.map (fun (pre,post) -> pre, preify srk tr_symbols post) (find_prepost []) in
    prepost_labels



  let get_pre_post_labels srk formula exists tr_symbols =
    let pre_symbols = pre_symbols tr_symbols in
    let post_symbols = post_symbols tr_symbols in
    let solver = Smt.mk_solver srk in
    let man = Polka.manager_alloc_strict () in
    let exists_pre x =
      exists x && not (Symbol.Set.mem x post_symbols)
    in
    let exists_post x =
      exists x && not (Symbol.Set.mem x pre_symbols)
    in
    let rec find_pre labels = 
      match Smt.Solver.get_model solver with
      | `Unsat -> labels
      | `Unknown -> assert false
      | `Sat m ->
        match Interpretation.select_implicant m formula with
        | None -> assert false
        | Some imp ->
          let pre_imp = SrkApron.formula_of_property (Abstract.abstract ~exists:exists_pre srk man (mk_and srk imp)) in
          Smt.Solver.add solver [mk_not srk pre_imp];
          find_pre (pre_imp :: labels)
    in
    let rec find_post labels = 
      match Smt.Solver.get_model solver with
      | `Unsat -> labels
      | `Unknown -> assert false
      | `Sat m ->
        match Interpretation.select_implicant m formula with
        | None -> assert false
        | Some imp -> 
          let post_imp = SrkApron.formula_of_property (Abstract.abstract ~exists:exists_post srk man (mk_and srk imp)) in
          Smt.Solver.add solver [mk_not srk post_imp];
          find_post (post_imp :: labels)
    in
    Smt.Solver.reset solver;
    Smt.Solver.add solver [formula];
    let pre_labels = find_pre [] in
    Smt.Solver.reset solver;
    Smt.Solver.add solver [formula];
    let post_labels = List.map (fun lab -> preify srk tr_symbols lab) (find_post []) in
    pre_labels, post_labels


  let get_pre_cube_labels srk formula exists tr_symbols =
    Log.errorf "Error in cube?";
    let pre_symbols = pre_symbols tr_symbols in
    let post_symbols = post_symbols tr_symbols in
    let solver = Smt.mk_solver srk in
    let exists_pre x =
      exists x && not (Symbol.Set.mem x post_symbols)
    in
    let exists_post x =
      exists x && not (Symbol.Set.mem x pre_symbols)
    in
    let rec find_pre labels =
      Log.errorf "whyyy";
      match Smt.Solver.get_model solver with
      | `Unsat -> labels
      | `Unknown -> assert false
      | `Sat m ->
        match Interpretation.select_implicant m formula with
        | None -> assert false
        | Some imp ->
          (*let imp = [Nonlinear.linearize srk (mk_and srk imp)] in*) (*Does this change abstraction*)
          Log.errorf "entry";
          let pre_imp = Q.local_project_cube srk exists_pre m imp in
          Smt.Solver.add solver [mk_not srk (mk_and srk pre_imp)];
          Log.errorf "exit";
          Log.errorf "Num: %d" (List.length labels);
          find_pre ((preify srk tr_symbols (mk_and srk pre_imp)) :: labels)
    in
    Smt.Solver.reset solver;
    Smt.Solver.add solver [SrkSimplify.simplify_terms srk formula];
    let pre_labels = find_pre [] in
    let post_form = (rewrite srk ~down:(nnf_rewriter srk) 
                       (mk_and srk [formula; mk_not srk (postify srk tr_symbols (mk_or srk pre_labels))])) in
    Log.errorf "Here";
    let rec find_post labels =
      Log.errorf "yEEE";
      match Smt.Solver.get_model solver with
      | `Unsat -> labels
      | `Unknown -> assert false
      | `Sat m ->
        match Interpretation.select_implicant m post_form with
        | None -> assert false
        | Some imp ->
          (*let imp = [Nonlinear.linearize srk (mk_and srk imp)] in*)
          let post_imp = Q.local_project_cube srk exists_post m imp in
          Smt.Solver.add solver [mk_not srk (mk_and srk post_imp)];
          Log.errorf "exit";
          Log.errorf "Post lab Num: %d" (List.length labels);
          find_post ((preify srk tr_symbols (mk_and srk post_imp)) :: labels)
    in
    Smt.Solver.reset solver;
    Smt.Solver.add solver [post_form];
    let post_labels = find_post [] in
    pre_labels, post_labels


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

  let get_intersect_labeling srk formula exists tr_symbols =
    let pre, post = get_pre_post_labels srk formula exists tr_symbols in
    let pre', post' = get_largest_polyhedrons srk pre, get_largest_polyhedrons srk post in
    List.iteri (fun ind lab -> Log.errorf "PRE LABEL NUM %d: %a" ind (Formula.pp srk) (lab)) pre';
    List.iteri (fun ind lab -> Log.errorf "POST LABEL NUM %d: %a" ind (Formula.pp srk) (lab)) post;

    let remain_post = mk_and srk
        [mk_or srk post;
         mk_not srk (mk_or srk pre')] in(*might be nice to make remain_post polyhedron*)
    let result = BatArray.of_list (remain_post :: pre') in
    Array.iteri (fun ind lab -> Log.errorf "LABEL NUM %d: %a" ind (Formula.pp srk) (SrkSimplify.simplify_terms srk lab)) result;
    result


  let get_intersect_cube_labeling srk formula exists tr_symbols =
    let pre, post = get_pre_cube_labels srk formula exists tr_symbols in
    List.iteri (fun ind lab -> Log.errorf "PRE LABEL NUM %d: %a" ind (Formula.pp srk) (lab)) pre;
    List.iteri (fun ind lab -> Log.errorf "POST LABEL NUM %d: %a" ind (Formula.pp srk) (lab)) post;
    Log.errorf "BREAK HERE______________";
    let pre', post' = get_largest_polyhedrons srk pre, get_largest_polyhedrons srk post in
    List.iteri (fun ind lab -> Log.errorf "PRE LABEL NUM %d: %a" ind (Formula.pp srk) (lab)) pre';
    List.iteri (fun ind lab -> Log.errorf "POST LABEL NUM %d: %a" ind (Formula.pp srk) (lab)) post';
    let result = BatArray.of_list (post' @ pre') in
    Array.iteri (fun ind lab -> Log.errorf "LABEL NUM %d: %a" ind (Formula.pp srk) (SrkSimplify.simplify_terms srk lab)) result;
    result




  let abstract ?(exists=fun x -> true) srk tr_symbols body =
    Log.errorf "Body formula: %a" (Formula.pp srk) body;
    let body = (rewrite srk ~down:(nnf_rewriter srk) body) in
    let body = Nonlinear.linearize srk body in (*Does this change abstraction*)
    let vas = abstract ~exists srk tr_symbols body in
    match vas with
    | {v; alphas;invars;invarmaxk} ->
      let body,cinvars,maxk = find_invariants srk tr_symbols body in
      Log.errorf "NUM ALPHAS %d" (List.length alphas);
      (*let label = deterministic_phase_label srk body exists tr_symbols alphas v in*)
      let label = get_intersect_cube_labeling srk body exists tr_symbols in
      let simulation = alphas in
      let graph = compute_edges srk v tr_symbols alphas label body in
      BatArray.iteri (fun ind arr -> 
          BatArray.iteri (fun ind2 trans ->
              Log.errorf "Num connections from label %d to label %d is: %d" ind ind2 (TSet.cardinal trans)) arr) graph;
      {label; graph; simulation; invars=invars @ cinvars; invarmaxk}



  (*The N vars are the max number of times any transition was taken. Used for flow primarily*)
  let rec create_n_vars srk num vars basename =
    begin match num <= 0 with
      | true -> List.rev vars (*rev only to make debugging easier and have names match up... not needed *)
      | false -> create_n_vars srk (num - 1) ((mk_symbol srk ~name:(basename^(string_of_int num)) `TyInt) :: vars) basename
    end

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

  (*ESL entry node for graph; ETL exit node for graph*)
  let create_es_et srk num =
    let es = map_terms srk (create_n_vars srk num [] "ESL") in
    let et = map_terms srk (create_n_vars srk num [] "ETL") in
    List.combine es et


  (* in_sing is which transformers enter single label; out single is which transformers exit single label
   * in_scc is which transformers enter scc; pre_scc is which transformers originate in given scc*)
  let exp_compute_trans_in_out_index_numbers transformersmap num sccs nvarst =
    let num_sccs, func_sccs = sccs in
    let in_sing, out_sing, in_scc, pre_scc = Array.make num [], Array.make num [], Array.make num_sccs [], Array.make num_sccs [] in
    List.iteri (fun index (n1, trans, n2) -> in_sing.(n2)<-((List.nth nvarst index) :: in_sing.(n2)); out_sing.(n1)<- ((List.nth nvarst index) :: out_sing.(n1));
                 pre_scc.(func_sccs n1)<- ((List.nth nvarst index) :: pre_scc.(func_sccs n1));
                 if not (func_sccs n1 = func_sccs n2) then begin 
                   in_scc.(func_sccs n2)<-((List.nth nvarst index) :: in_scc.(func_sccs n2)) 
                 end)
      transformersmap;
    in_sing, out_sing, in_scc, pre_scc


  (* in_sing is which transformers enter single label; out single is which transformers exit single label
   * in_scc is which transformers enter scc; pre_scc is which transformers originate in given scc*)
  let exp_compute_trans_in_out_index_numbers transformersmap num sccs nvarst =
    let num_sccs, func_sccs = sccs in
    let in_sing, out_sing, in_scc, pre_scc = Array.make num [], Array.make num [], Array.make num_sccs [], Array.make num_sccs [] in
    List.iteri (fun index (n1, trans, n2) -> in_sing.(n2)<-(index :: in_sing.(n2)); out_sing.(n1)<- (index :: out_sing.(n1));
                 pre_scc.(func_sccs n1)<- (index :: pre_scc.(func_sccs n1));
                 if not (func_sccs n1 = func_sccs n2) then begin 
                   in_scc.(func_sccs n2)<-(index :: in_scc.(func_sccs n2)) 
                 end)
      transformersmap;
    in_sing, out_sing, in_scc, pre_scc

  (*Compute the condition that must hold if a given transformer is taken*)
  let compute_trans_post_cond srk prelabel postlabel (trans : transformer) (rtrans,rverts) alphas tr_symbols lc ind = 
    let term_list = term_list srk alphas tr_symbols in
    let f' = TSet.fold (fun t acc -> mk_or srk [(gamma_transformer srk term_list t); acc]) rtrans (mk_false srk) in
    let pre_symbols = pre_symbols tr_symbols in
    let post_symbols = post_symbols tr_symbols in
    let man = Polka.manager_alloc_strict () in
    let exists_post x = not (Symbol.Set.mem x pre_symbols) in
    let trans' = gamma_transformer srk term_list trans in
    let ptrans_form = (rewrite srk ~down:(nnf_rewriter srk) (mk_and srk [prelabel;trans';postlabel])) in
    Log.errorf "Error here?";
    let post_trans = SrkApron.formula_of_property (Abstract.abstract ~exists:exists_post srk man ptrans_form) in
    (*if TSet.is_empty rtrans then post_trans else *)
    let loop_counter = mk_const srk (mk_symbol srk ~name:("Trans_Counter"^(string_of_int ind)) `TyInt) in
    let lri_form = (rewrite srk ~down:(nnf_rewriter srk) f') in 
    (*let lri = LRI.exp srk tr_symbols loop_counter (LRI.abstract srk tr_symbols lri_form) in
      let pg = PG.postcondition (PG.abstract srk tr_symbols lri_form) in*)
    let rslt = SrkApron.formula_of_property
        (Abstract.abstract ~exists:exists_post srk man (*Add new loop counter into exists?*)
           (mk_and srk
              [preify srk tr_symbols post_trans;
               Accelerate.closure (Accelerate.abstract srk tr_symbols lri_form)
               (*lri;
                 SrkApron.formula_of_property pg*)]))
    in
    let rslt = mk_and srk [rslt; mk_lt srk (mk_zero srk) loop_counter; mk_leq srk loop_counter lc] in
    rslt


  (* If a transformers is taken, that transformer post condition must hold*)
  let exp_post_conds_on_transformers srk label transformersmap reachability nvarst alphas tr_symbols lc =
    mk_and srk 
      (BatList.mapi (fun ind (n1, trans, n2) -> 
           let post_cond = compute_trans_post_cond srk label.(n1) (postify srk tr_symbols label.(n2)) 
               trans reachability.(n2) alphas tr_symbols lc ind in
           Log.errorf "Pos %d post cond is %a" ind (Formula.pp srk) post_cond;
           mk_if srk (mk_lt srk (mk_zero srk) (List.nth nvarst ind)) (mk_and srk [post_cond; mk_true srk])) transformersmap
      ) 

  (* Flow is conserved for the nvarst *)
  let exp_consv_of_flow_new srk in_sing out_sing ests varst reset_label =
    let in_sing_inds = in_sing in
    let in_sing = BatArray.map (fun indlist -> List.map (fun ind -> List.nth varst ind) indlist) in_sing in
    let out_sing = BatArray.map (fun indlist -> List.map (fun ind -> List.nth varst ind) indlist) out_sing in
    mk_and srk
      (List.mapi (fun ind (es, et) ->
           mk_eq srk
             (mk_add srk ((if reset_label = -2 then es else if (BatList.mem reset_label in_sing_inds.(ind)) 
                           then mk_one srk else mk_zero srk) :: in_sing.(ind)))
             (mk_add srk (et :: out_sing.(ind))))
          ests)

  let exp_consv_of_flow srk in_sing out_sing ests =
    let extra_one = -2 in
    mk_and srk
      (List.mapi (fun ind (es, et) ->
           mk_eq srk
             (mk_add srk ((if extra_one = -2 then es else if extra_one = ind then mk_one srk else mk_zero srk) :: in_sing.(ind)))
             (mk_add srk (et :: out_sing.(ind))))
          ests)



  (*Either there is an entry node and exit node, or no transitions taken*)
  let exp_one_in_out_flow srk ests nvarst = 
    let et, es = List.split ests in
    mk_or srk
      [mk_and srk 
         [mk_eq srk (mk_add srk et) (mk_one srk);
          mk_eq srk (mk_add srk es) (mk_one srk)];
       mk_eq srk (mk_add srk nvarst) (mk_zero srk)]

  (* Each es and et var either 1 or 0. If a single label, both 1 or both 0 *)
  let exp_each_ests_one_or_zero srk ests =
    if (List.length ests = 1) then
      (
        let (es, et) = List.hd ests in
        mk_or srk [mk_and srk [mk_eq srk es (mk_one srk); mk_eq srk et (mk_one srk)];
                   mk_and srk [mk_eq srk es (mk_zero srk); mk_eq srk et (mk_zero srk)]]
      )
    else(
      mk_and srk
        (List.map (fun (es, et) -> 
             mk_and srk
               [mk_or srk [mk_eq srk es (mk_zero srk); mk_eq srk es (mk_one srk)];
                mk_or srk [mk_eq srk et (mk_zero srk); mk_eq srk et (mk_one srk)]]
           )
            ests))

  (* The initial label for graph must have precond satisfied; the final label for graph must have 
   * post cond satisfied*)
  let exp_pre_post_conds srk ests label tr_symbols =
    mk_and srk
      (List.mapi (fun ind (es, et) ->
           mk_and srk
             [mk_if srk (mk_eq srk es (mk_one srk)) (label.(ind));
              mk_if srk (mk_eq srk et (mk_one srk)) (postify srk tr_symbols (label.(ind)))])
          ests)

  (* If an scc is never entered, all transformers originating in that scc are never taken*)
  let exp_never_enter_scc_new srk ests in_scc pre_scc sccs varst extra_num =
    let num_sccs, func_sccs = sccs in
    let es_comp = Array.make num_sccs [] in
    let in_scc_inds = in_scc in
    let in_scc = BatArray.map (fun indlist -> List.map (fun ind -> List.nth varst ind) indlist) in_scc in 
    let pre_scc = BatArray.map (fun indlist -> List.map (fun ind -> List.nth varst ind) indlist) pre_scc in 
    List.iteri (fun ind eset -> es_comp.(func_sccs ind)<-(eset :: (es_comp.(func_sccs ind)))) ests;
    mk_and srk
      (Array.to_list
         (Array.mapi (fun ind in_scc_comp ->
              mk_if srk
                (mk_eq srk
                   (mk_add srk
                      [mk_add srk (if extra_num = -2 then (List.map (fun (es, et) -> es) (es_comp.(ind)))
                                   else if (List.mem extra_num (in_scc_inds.(ind))) then [mk_one srk]
                                   else [mk_zero srk]);
                       mk_add srk (in_scc_comp)])
                   (mk_zero srk))
                (mk_eq srk
                   (mk_add srk
                      [mk_add srk (List.map (fun (es,et) -> et) (es_comp.(ind)));
                       (mk_add srk (pre_scc.(ind)))])
                   (mk_zero srk)))
             in_scc))
  let exp_never_enter_scc srk ests in_scc pre_scc sccs =
    let num_sccs, func_sccs = sccs in
    let es_comp = Array.make num_sccs [] in
    let in_scc_inds = in_scc in
    let extra_num = -2 in
    List.iteri (fun ind eset -> es_comp.(func_sccs ind)<-(eset :: (es_comp.(func_sccs ind)))) ests;
    mk_and srk
      (Array.to_list
         (Array.mapi (fun ind in_scc_comp ->
              mk_if srk
                (mk_eq srk
                   (mk_add srk
                      [mk_add srk (List.map (fun (es, et) -> es) (es_comp.(ind)));
                       mk_add srk (in_scc_comp)])
                   (mk_zero srk))
                (mk_eq srk
                   (mk_add srk
                      [mk_add srk (List.map (fun (es,et) -> et) (es_comp.(ind)));
                       (mk_add srk (pre_scc.(ind)))])
                   (mk_zero srk)))
             in_scc))



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

  (*Either svar for each row in equiv class in x and equiv class not reset or equiv class reset
   * at transformer i and svars equal the reset dim at transformer i*)
  let exp_sx_constraints_helper_flow srk ri ksum ksums svarstdims transformers kvarst unialpha tr_symbols kstack in_sing
      out_sing ests in_scc pre_scc sccs =
    let compute_single_svars svart dim  =
      mk_or srk
        ((mk_and srk
            [(mk_eq srk svart (preify srk tr_symbols (Linear.of_linterm srk (M.row dim unialpha)))); (*pivot or row? need to make sure alpha and dim both indexed same *)
             (mk_eq srk ri (mk_real srk (QQ.of_int (-1))))
             (*(MAKE KSUM = N NUM)*)]) ::
         (BatList.mapi 
            (fun ind {a; b} ->
               if ZZ.equal (Z.coeff dim a) ZZ.one 
               then (mk_false srk)
               else 
                 mk_and srk
                   [(mk_eq srk svart (mk_real srk (V.coeff dim b)));
                    exp_other_reset srk ksum ksums kvarst ind;
                    (mk_eq srk ri (mk_real srk (QQ.of_int ind)));
                    exp_consv_of_flow_new srk in_sing out_sing ests kstack ind;
                    exp_never_enter_scc_new srk ests in_scc pre_scc sccs kstack ind
                    (*(MAKE FLOW FOR ONE K CLASS MAKe SeNSE kstack in_scc pre_scc in_sing out_sing)*)])
            transformers))
    in
    mk_and srk (List.map (fun (svar,dim) -> compute_single_svars svar dim) svarstdims)


  (*See helper function for description*)
  let exp_sx_constraints_flow srk equiv_pairs transformers kvarst ksums unialpha tr_symbols in_sing out_sing ests in_scc pre_scc sccs =
    mk_and srk
      (List.map (fun (kstack, svarstdims, ri, ksum) ->
           exp_sx_constraints_helper_flow srk ri ksum ksums svarstdims transformers kvarst unialpha tr_symbols kstack in_sing out_sing ests
             in_scc pre_scc sccs)
          equiv_pairs)



  let exp srk tr_symbols loop_counter vassabs =
    match vassabs with
    | {label; graph; simulation; invars;invarmaxk} ->
      let alphas = simulation in
      if(M.nb_rows (unify alphas) = 0) then mk_true srk else (
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
        let (form, (equiv_pairst, kvarst, svarst, rvarst, ksumst)) =
          exp_base_helper srk tr_symbols loop_counter simulation transformers invars invarmaxk true in
        let sum_n_eq_loop_counter = exp_nvars_eq_loop_counter srk nvarst loop_counter in
        let ks_less_than_ns = exp_kvarst_less_nvarst srk nvarst kvarst in
        let sccs = GraphComp.scc graph in
        let reachable_transitions = get_reachable_trans graph in
        BatArray.iteri (fun ind (trans, verts) -> 
            TSet.iter (fun trans ->
                Log.errorf "Label %d admits trans %a" ind (Transformer.pp) trans) trans;
            BatList.iter (fun vert ->
                Log.errorf "Label %d trans to label %d" ind vert) verts) 
          reachable_transitions;
        let post_conds_const = exp_post_conds_on_transformers srk label transformersmap reachable_transitions nvarst alphas tr_symbols loop_counter in

        let in_sing, out_sing, in_scc, pre_scc = exp_compute_trans_in_out_index_numbers transformersmap (Array.length label) sccs nvarst in
        let ests = create_es_et srk (Array.length label) in
        let flow_consv_req = exp_consv_of_flow_new srk in_sing out_sing ests nvarst (-2) in
        let in_out_one = exp_one_in_out_flow srk ests nvarst in
        let ests_one_or_zero = exp_each_ests_one_or_zero srk ests in
        let pre_post_conds = exp_pre_post_conds srk ests label tr_symbols in
        let never_enter_constraints = exp_never_enter_scc_new srk ests in_scc pre_scc sccs nvarst (-2) in
        let pos_constraints = create_exp_positive_reqs srk [nvarst; fst (List.split ests); snd (List.split ests)] in
        let sx_constraints = exp_sx_constraints_flow srk equiv_pairst transformers kvarst ksumst (unify alphas) tr_symbols in_sing out_sing
            ests in_scc pre_scc sccs in
        Log.errorf " Failure cause %a" (Formula.pp srk) pre_post_conds;
        let form = mk_and srk [form; sum_n_eq_loop_counter; ks_less_than_ns; flow_consv_req; in_out_one;
                               ests_one_or_zero;  pre_post_conds; never_enter_constraints; pos_constraints; post_conds_const(*; sx_constraints*)] in
        Log.errorf " Current D VAL %a" (Formula.pp srk) form;
        form
      )
end

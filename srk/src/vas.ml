open Syntax
open BatPervasives
module V = Linear.QQVector
module M = Linear.QQMatrix
module Z = Linear.ZZVector
module H = Abstract
include Log.Make(struct let name = "srk.vas" end)

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
 * and a list of linear simulations matrices, s_lst.
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
 *)
type 'a t = { v : vas; s_lst : M.t list}

(* This function is used to stack the matrices
 * on top of each other to form a single matrix.
 * Each matrix must start at
 * row 0. No row may be 0.
 * The matrices are stacked sequentially, with the first
 * matrix corresponding to the first rows of the output matrix.
 *)
let unify matrices =
  BatList.enum matrices
  /@ M.rowsi
  |> BatEnum.concat
  |> BatEnum.map snd
  |> BatList.of_enum
  |> M.of_rows

(* Similar to above, stacks matrices and vectors.
 * Must be same number of matrices and vectors.
 * Matrix i must have same number of rows as vector i.
*)
let unify2 matrices vects =
  let unified = List.fold_left2 (fun (acc_matrix, v) matr b -> 
      BatEnum.fold (fun (acc_matrix, v) (dim, term) ->
          M.add_row (M.nb_rows acc_matrix) term acc_matrix,
          V.add_term (V.coeff dim b) (M.nb_rows acc_matrix) v)
        (acc_matrix, v)
        (M.rowsi matr))
      (M.zero,V.zero) matrices vects in
  unified

let mk_top = {v=TSet.empty; s_lst=[]}

let mk_bottom srk tr_symbols symb_constants =
  (* Matrix in which 1 row for each sym in * tr_symbols; row has a 1
     exactly in the col for corresponding sym'*)
  let double_symb = List.map (fun x -> (x, x)) symb_constants in
  let sim =
    List.map (fun (_, x') -> V.of_term QQ.one (Linear.dim_of_sym x')) (tr_symbols @ double_symb)
    |> M.of_rows
  in
  {v=TSet.empty; s_lst=[sim]}


(* Used in preify and postify to create symbol map.
 * Is a way to substitute variables; for example
 * x with x' or x' with x.
 *)
let post_map srk tr_symbols =
  List.fold_left
    (fun map (sym, sym') -> Symbol.Map.add sym (mk_const srk sym') map)
    Symbol.Map.empty
    tr_symbols

(* For tr_symbols list of form (x, x'),
 * replace x' with x in term.
 *)
let preify srk tr_symbols = substitute_map srk
    (post_map srk (List.map (fun (x, x') -> (x', x)) tr_symbols))

(* Same as preify, but replaces x with x' *)
let postify srk tr_symbols = substitute_map srk (post_map srk tr_symbols)

(* Ki,j is number of times equiv class i took transformer j
 * Ri is the transformer equiv class i was reset on (-1 if never reset)
 * Si,j is the starting value for linear term row j of equiv class i matrix
 * Each S var is also associated with dimension in unified VAS Abstraction;
 * bdim keeps track of this
 * Kstack[i] is just list of Ki,j vars for all j
 * KSUMi is sum of Ki,j vars for all j
 * equiv_pair groups all kinds of vars together for a given equiv class
 *)
let create_exp_vars srk s_lst transformers =
  let bdim = ref 0 in
  let mk_constants nb basename (typ : Syntax.typ) =
    (0 -- (nb - 1))
    /@ (fun i ->
        let name = Format.sprintf "%s,%d" basename i in
        mk_const srk (mk_symbol srk ~name typ))
    |> BatList.of_enum
  in
  let rec helper s_lst coh_rep coh_class_pairs =
    (* coh_rep is coherence class representative *)
    match s_lst with
    | [] -> coh_class_pairs
    | hd :: tl -> 
      (* Create K vars. *)
      let kstack =
        List.mapi (fun i tr ->
            (* If transformer j resets coherence class i, kvari,j is 0. *)
            if ZZ.equal ZZ.zero (Z.coeff coh_rep tr.a) then
              mk_zero srk
            else
              let name = Format.sprintf "K%d,%d" (List.length s_lst) i in
              mk_const srk (mk_symbol srk ~name `TyInt))
          transformers
      in
      (*Create R vars*)
      let rvar =
        (* If no transformer resets coherence class i, r_i is -1. *)
        if List.exists (fun tr -> ZZ.equal ZZ.zero (Z.coeff coh_rep tr.a)) transformers then
          mk_const srk  (mk_symbol srk ~name:("R"^(string_of_int (List.length s_lst))) `TyInt)
        else
          mk_real srk (QQ.of_int (-1))
      in
      (*Create KSum vars*)
      let ksum =
        mk_const srk (mk_symbol srk ~name:("KSUM"^(string_of_int (List.length s_lst))) `TyInt)
      in

      (*Create S vars*)
      let svar =
        mk_constants (M.nb_rows hd) ("S" ^ (string_of_int (List.length s_lst))) `TyReal
      in

      (*Group vars together*)
      let equiv_pair = (kstack, 
                        List.map (fun svar -> 
                            let res = (svar, !bdim) in incr bdim; res)
                          svar,
                        rvar, ksum) in
      helper tl (coh_rep + (M.nb_rows hd)) (equiv_pair :: coh_class_pairs)
  in
  helper s_lst 0 []

(* Make input terms each >= 0 *)
let mk_all_nonnegative srk terms =
  terms
  |> List.map (mk_leq srk (mk_zero srk))
  |> mk_and srk


let mk_nat_leq srk x y =
  match Term.destruct srk x, Term.destruct srk y with
  | (`Real k, _) when QQ.equal k QQ.zero -> mk_true srk
  | (_, `Real k) when QQ.equal k QQ.zero -> mk_eq srk x (mk_zero srk)
  | (_, _) -> mk_leq srk x y

(* Determine if equiv class was never reset (number
 * transitions taken == number steps taken).
 * In this case, its corresponding reset var is set to -1.
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

(* Pair each coherence class *)
let all_pairs_kvarst_rvarst ksumst kvarst rvarst =
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
    | khd :: ktl, ksthd :: ksttl, rhd :: rtl -> 
      (helper1 (khd, ksthd, rhd) ktl ksttl rtl) :: (helper2 ktl ksttl rtl)
    | _ -> assert false
  in
  List.flatten (helper2 ksumst kvarst rvarst)

(* Create every permutation of ordering for coherence classes *)
let exp_perm_constraints srk krpairs =
  mk_and srk
    (List.map 
       (fun (_, k1, _, _, k2, _) -> 
          let lessthan k1 k2 = mk_and srk 
              (List.map2 (fun k1' k2' -> mk_nat_leq srk k1' k2') k1 k2)
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


(*If ksumi less than ksumj, coh class j
 * took transformer that coh class i reset on at least once*)
let exp_other_reset_helper srk ksumi ksums kvarst trans_num =
  mk_and srk
    (List.mapi (fun ind ksum' ->
         (mk_if srk
            (mk_lt srk ksumi ksum')
            (mk_leq srk
               (mk_one srk)
               (List.nth (List.nth kvarst ind) trans_num))))
        ksums)


(*This function sets the initial value for each dimension of an equiv class.
 * Initial values for dimensions of same equiv class must correspond
 * to same transformer reset. This is also where the above function,
 * exp_other_reset_helper, is used to enforce that a given transformer
 * is taken by equiv classes that having been running for more time without
 * a reset.
 *)
let exp_sx_constraints_helper srk ri ksum ksums svarstdims transformers kvarst 
    unified_s tr_symbols =
  let compute_single_svars svart dim  =
    mk_or srk
      (*The never reset case*)
      ((mk_and srk
          [(mk_eq srk svart (preify srk tr_symbols 
                               (Linear.of_linterm srk (M.row dim unified_s))));
           (mk_eq srk ri (mk_real srk (QQ.of_int (-1))))]) 
       (*The reset case*)
       ::
       (BatList.mapi 
          (fun ind {a; b} ->
             if ZZ.equal (Z.coeff dim a) ZZ.one 
             then (mk_false srk) (*May be nicer to filter these out prior to creating
                                   smt query*) 
             else 
               mk_and srk
                 [(mk_eq srk svart (mk_real srk (V.coeff dim b)));
                  exp_other_reset_helper srk ksum ksums kvarst ind;
                  (mk_eq srk ri (mk_real srk (QQ.of_int ind)))])
          transformers))
  in
  mk_and srk (List.map (fun (svar,dim) -> compute_single_svars svar dim) svarstdims)

(*Uses sx_constraints_helper to set initial values for each dimension of each equiv class*)
let exp_sx_constraints srk coh_class_pairs transformers kvarst ksums unified_s tr_symbols =
  mk_and srk
    (List.map (fun (kstack, svarstdims, ri, ksum) ->
         exp_sx_constraints_helper srk ri ksum ksums svarstdims transformers 
           kvarst unified_s tr_symbols)
        coh_class_pairs)


(*Constraints for equalities of final termination value for each linear term*)
let exp_lin_term_trans_constraints srk coh_class_pairs transformers unified_s =
  mk_and srk
    (List.map (fun (kstack, svarstdims, ri, _) ->
         mk_and srk
           (List.map (fun (svar, dim) ->
                mk_eq srk
                  (Linear.of_linterm srk (M.row dim unified_s))
                  (mk_add srk
                     (svar :: 
                      (BatList.mapi
                         (fun ind {a; b} ->
                            mk_mul srk 
                              [(List.nth kstack ind); mk_real srk (V.coeff dim b)])
                         transformers))))
               svarstdims))
        coh_class_pairs)

(*No coh class can take more trans than loop counter*)
let exp_kstacks_at_most_k srk ksumst loop_counter=
  List.map (fun ksum -> mk_leq srk ksum loop_counter) ksumst
  |> mk_and srk

(*Relate KSumi with Ki,j vars*)
let exp_kstack_eq_ksums srk coh_class_pairs =
  mk_and srk
    (List.map (fun (kstack, _, _, ksum) ->
         mk_eq srk (mk_add srk kstack) ksum)
        coh_class_pairs)

(*Combines all of the closure constraints that are used
 * in both VAS and VASS abstractions
 *)
let exp_base_helper srk (tr_symbols : (symbol * symbol) list) loop_counter s_lst transformers =
 (*Create new symbols
  * Each coh class has:
  * a set of kvars, where the ith coh class jth kvar is
  * the number of times that coh class i took the jth transformer since last reset
  * an rvar, where the ith coh class rvar = j for j >= 0 means that coh class i
  * took last reset on transformer j; rvar = -1 means coh class i never reset
  * a list of the form (s,d), where the the jth (s, d) in this list has the property
  * that s is the starting value for the jth row of coh class i (after last reset),
  * and d is the dim of this row in the unified simulation*)
  let coh_class_pairs = create_exp_vars srk s_lst transformers in
  let kvarst, rvarst, ksumst = List.map (fun (kstack, _, _, _) -> kstack) coh_class_pairs, 
                               List.map (fun (_, _, rvarst, _) -> rvarst) coh_class_pairs,
                               List.map (fun (_, _, _, ksumst) -> ksumst) coh_class_pairs in
  let krpairs = all_pairs_kvarst_rvarst ksumst kvarst rvarst in

  let constr1 = mk_all_nonnegative srk (loop_counter :: (List.flatten kvarst)) in
  let constr2 = exp_full_transitions_reqs srk kvarst rvarst loop_counter in
  let constr3 = exp_perm_constraints srk krpairs in
  let constr4 = exp_equality_k_constraints srk krpairs in
  let constr5 = exp_kstacks_at_most_k srk ksumst loop_counter in
  let constr6 = exp_lin_term_trans_constraints srk coh_class_pairs 
      transformers (unify s_lst) in
  let constr7 = exp_kstack_eq_ksums srk coh_class_pairs in
 let formula = 
    mk_and srk 
      [constr1; constr2; constr3; constr4; constr5; constr6; constr7] in
  (formula, (coh_class_pairs, kvarst, ksumst))


(*Compute closure*)
let exp srk tr_symbols loop_counter vabs =
  let {v; s_lst} = vabs in
  (* if top*)  
  if(M.nb_rows (unify s_lst) = 0) 
  then mk_true srk
  else (
    let (formula, (coh_class_pairs, kvarst, ksumst)) = exp_base_helper srk tr_symbols
        loop_counter s_lst (TSet.to_list v) in
    let constr1 = exp_sx_constraints srk coh_class_pairs
        (TSet.to_list v) kvarst ksumst (unify s_lst) tr_symbols in
    mk_and srk [formula; constr1]
  )


(*Move matrix down by first_row rows*)
let push_rows matrix first_row =
  BatEnum.fold 
    (fun matrix (dim', row) ->  M.add_row (dim' + first_row) row matrix) 
    M.zero 
    (M.rowsi matrix)


let coprod_find_transformation s_lst1 s_lst2 =
  (*Offsets make sure we take intersections of coh classes
   * using proper location in unified matrix
   *)
  let offset1 = ref 0 in
  (*r1 is transformation from s_lst1 to s_lst;
   *r2 is transformation from s_lst2 to s_lst
   *)
  let r1, r2, s_lst =
    List.fold_left (fun (r1, r2, s_lst) cohclass1 -> 
        let offset2 = ref 0 in
        let r1', r2', s_lst' = 
          (List.fold_left (fun (r1', r2', s_lst') cohclass2 ->
               (*Adjust rows with offset*)
               let cohclass1, cohclass2 = (push_rows cohclass1 !offset1,
                                           push_rows cohclass2 !offset2) in
               let (u1, u2) = Linear.intersect_rowspace cohclass1 cohclass2 in
               offset2 := (M.nb_rows cohclass2) + !offset2;
               (*If matrix 0, no new coh class formed*)
               if M.equal u1 M.zero then (r1', r2', s_lst') 
               else (u1 :: r1', u2 :: r2', (M.mul u1 cohclass1) :: s_lst'))
              ([], [], []) s_lst2) in
        offset1 := (M.nb_rows cohclass1) + !offset1; 
        List.append r1' r1, List.append r2' r2, List.append s_lst' s_lst)
      ([], [], []) s_lst1
  in
  r1, r2, s_lst

(*Takes in vas and lin transformer and compute image*)
let coprod_compute_image v r =
  let unifr = unify r in
  (*Computes a representative dim for each coh class*)
  let rowreps = 
      BatList.map (fun (dim', row) ->
          match BatEnum.get (V.enum row) with
          | None -> assert false
          | Some (scalar, dim) -> dim
        )
        (BatList.of_enum (M.rowsi unifr))
  in
  (*image for single transformer*)
  let transformer_image t rowsreps =
    let a, b = t.a, t.b in
    let b' = M.vector_right_mul unifr b in
    let a' = BatList.fold_lefti (fun vector ind dim ->
        Z.add_term (Z.coeff dim a) ind vector
      )
        Z.zero
        rowsreps
    in
    {a=a'; b=b'}
  in
  let v' = TSet.fold (fun ele acc -> 
      TSet.add (transformer_image ele rowreps) acc) v TSet.empty in
  v'


let coproduct srk vabs1 vabs2 : 'a t =
  Log.errorf "coprod1";
  let (s_lst1, s_lst2, v1, v2) = (vabs1.s_lst, vabs2.s_lst, vabs1.v, vabs2.v) in
  Log.errorf "coprod2";
  let s1, s2, s_lst = coprod_find_transformation s_lst1 s_lst2 in
  Log.errorf "coprod3";
  let v = TSet.union (coprod_compute_image v1 s1) (coprod_compute_image v2 s2) in
  Log.errorf "coprod4";
  {v; s_lst}


(*List of terms in s_lst, preified and postified*)
let term_list srk s_lst tr_symbols = 
  List.map (fun matrix -> 
      ((M.rowsi matrix)
       /@ (fun (_, row) -> 
           let term = Linear.of_linterm srk row in
           (preify srk tr_symbols term, term)))
      |> BatList.of_enum)
    s_lst
  |> List.flatten

(*Turns a term list, prefied or postified, into matrix and col vector
 * for constants. Similar to inverse of above operation, but acts
 * on preified or postified
 *)
let matrixify_vectorize_term_list srk vl = 
  let add_dim m b term =
    let (b', v) = V.pivot (Linear.const_dim) (Linear.linterm_of srk term) in
    M.add_row (M.nb_rows m) v m, V.add_term (QQ.negate b') (M.nb_rows m) b
  in
  List.fold_left (fun (m, b) ele -> add_dim m b ele) (M.zero, V.zero) vl

(*Gamma of single transformer*)
let gamma_transformer srk term_list t =
  BatList.mapi (fun ind (pre_term, post_term) -> 
      mk_eq srk 
        post_term 
        (mk_add srk 
           [(mk_mul srk [pre_term; mk_real srk (QQ.of_zz (Z.coeff ind t.a))]);
            mk_real srk (V.coeff ind t.b)]))
    term_list
  |> mk_and srk

let gamma srk vas tr_symbols =
  let term_list = term_list srk vas.s_lst tr_symbols in
  if List.length term_list = 0 then mk_true srk else
    mk_or srk (List.map (fun t -> gamma_transformer srk term_list t) (TSet.elements vas.v))

let alpha_hat srk imp tr_symbols symb_constants =
  let double_symb = List.map (fun x -> (x, x)) symb_constants in 
  let (xdeltpairs, xdeltphis) = 
    List.split (List.fold_left (fun acc (x, x') -> 
        let xdeltpairs = (mk_symbol srk (typ_symbol srk x)) in
        let xdeltphis = (mk_eq srk (mk_const srk xdeltpairs) 
                                (mk_sub srk (mk_const srk x') (mk_const srk x))) in
        ((xdeltpairs, x'), xdeltphis) :: acc) [] (tr_symbols @ double_symb)) in
  let r, b1 = matrixify_vectorize_term_list srk 
      (H.affine_hull srk imp ((List.map (fun (x, x') -> x') tr_symbols) @ symb_constants)) in
  let i, b2 = matrixify_vectorize_term_list srk 
      (List.map (postify srk xdeltpairs)
         (H.affine_hull srk (mk_and srk (imp :: xdeltphis))
            (List.map (fun (x'', x') -> x'') xdeltpairs))) in
  let _, b = unify2 [i; r] [b2; b1] in
  let add_dim a offset =
    Z.add_term ZZ.one offset a
  in
  let a, _ = BatEnum.fold
      (fun (a, offset) _ -> (add_dim a offset, offset + 1))
      (Z.zero, 0) (M.rowsi i)
  in
  match M.equal r (M.zero), M.equal i (M.zero) with
  | true, true -> mk_top
  | false, true -> {v=TSet.singleton {a;b}; s_lst=[r]}
  | true, false ->  {v=TSet.singleton {a;b}; s_lst=[i]} 
  | false, false -> {v=TSet.singleton {a;b}; s_lst=[i;r]}

(*TODO:Make a better pp function*)
let pp srk syms formatter vas = Format.fprintf formatter "%a" (Formula.pp srk) (gamma srk vas syms)

let abstract ?(exists=fun x -> true) srk tr_symbols phi  =
  let tr_flat = List.fold_left (fun lst (x, x') -> x :: x' :: lst) [] tr_symbols in
  let symb_constants = Symbol.Set.elements
      (Symbol.Set.filter (fun a -> (exists a) && (not (List.mem a tr_flat))) (symbols phi)) in 
  let symb_eqs = List.fold_left (fun lst sym -> (mk_eq srk (mk_const srk sym) (mk_const srk sym)) :: lst) [] 
      symb_constants in
  let phi = mk_and srk (phi :: symb_eqs) in
  let phi = (rewrite srk ~down:(nnf_rewriter srk) phi) in
  let phi = Nonlinear.linearize srk phi in
  Log.errorf "formula is %a" (Formula.pp srk) phi;
 
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
        Log.errorf "frozen";
        let sing_transformer_vas = alpha_hat srk (mk_and srk imp) tr_symbols symb_constants in
        Log.errorf "passed";
        go (coproduct srk vas sing_transformer_vas)
  in
  Smt.Solver.add solver [phi];
  let {v;s_lst} = go (mk_bottom srk tr_symbols symb_constants) in
  let result = {v;s_lst} in
  result



let join  (srk :'a context) (tr_symbols : (symbol * symbol) list) (vabs1 : 'a t) (vabs2 : 'a t) = assert false
let widen  (srk :'a context) (tr_symbols : (symbol * symbol) list) (vabs1 : 'a t) (vabs2 : 'a t) = assert false
let equal (srk : 'a context) (tr_symbols : (symbol * symbol) list) (vabs1 : 'a t) (vabs2 : 'a t) = assert false

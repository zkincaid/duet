open Syntax
open BatPervasives

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

module CS = CoordinateSystem
module A = BatDynArray

module IntSet = SrkUtil.Int.Set
module H = Abstract
include Log.Make(struct let name = "srk.mdvas" end)

let qq_of_scalar = function
  | Scalar.Float k -> QQ.of_float k
  | Scalar.Mpqf k  -> k
  | Scalar.Mpfrf k -> Mpfrf.to_mpqf k

let qq_of_coeff = function
  | Coeff.Scalar s -> Some (qq_of_scalar s)
  | Coeff.Interval _ -> None

let qq_of_coeff_exn = function
  | Coeff.Scalar s -> qq_of_scalar s
  | Coeff.Interval _ -> invalid_arg "qq_of_coeff_exn: argument must be a scalar"

let coeff_of_qq = Coeff.s_of_mpqf

let scalar_zero = Coeff.s_of_int 0
let scalar_one = Coeff.s_of_int 1

let mk_log = Nonlinear.mk_log
let mk_pow = Nonlinear.mk_pow

let vec_of_poly = P.vec_of ~const:CS.const_id
let poly_of_vec = P.of_vec ~const:CS.const_id

let get_manager =
  let manager = ref None in
  fun () ->
    match !manager with
    | Some man -> man
    | None ->
      let man = Polka.manager_alloc_strict () in
      manager := Some man;
      man

(* Associate coordinates with apron dimensions.  Wedges may share coordinate
    systems, but should *not* share environments -- if the coordinate system
    of a wedge is updated, the wedge is brought back in sync using its
    environment (see update_env). *)
type env = { int_dim : int A.t;
             real_dim : int A.t }

let copy_env env =
  { int_dim = A.copy env.int_dim;
    real_dim = A.copy env.real_dim }

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

type vas_abs = { v : vas; alphas : M.t list }
[@@deriving show]

type vas_abs_lift = Vas of vas_abs | Top | Bottom
[@@deriving show]

type 'a t = vas_abs_lift

let pp _ _ = pp_vas_abs_lift

(*let linterm_swap (srk : 'a context) (term : 'a term) (map : (symbol, symbol) Hashtbl.t) : 'a term =
  let alg = function
    | `Real qq -> mk_real srk qq
    | _ -> mk_real srk QQ.zero
    (*| `App (func, args) -> `App (func, args)
    | `Var (v, `TyInt) -> (v, TyInt)
    | _ -> 
    | `Add sum -> List.fold_left add zero sum
    | `Mul sum -> List.fold_left mul (real QQ.one) sum
    | `Binop (`Div, x, y) -> scalar_mul (QQ.inverse (nonzero_qq_of y)) x
    | `Binop (`Mod, x, y) -> real (QQ.modulo (qq_of x) (nonzero_qq_of y))
    | `Unop (`Floor, x) -> real (QQ.of_zz (QQ.floor (qq_of x)))
    | `Unop (`Neg, x) -> negate x
    | `Ite (_, _, _) -> raise Nonlinear*)
  in
  Term.eval srk alg term
*)


let time marker =
    Printf.printf "Execution time at %s : %fs\n" marker (Sys.time());()

let unify (alphas : M.t list) : M.t =
  (*let rows, unified =
    List.fold_left (fun (rows, unified) alpha ->
      let rows', unified' = M.row_set alpha, M.add unified alpha in
      assert (SrkUtil.Int.Set.is_empty (SrkUtil.Int.Set.inter rows rows'));
      SrkUtil.Int.Set.union rows' rows, unified) (SrkUtil.Int.Set.empty, M.zero) alphas
  in*)
  let unified = List.fold_left (fun matrix alphacell -> 
      BatEnum.fold (fun matrix (dim, vector) ->
          M.add_row (M.nb_rows matrix) vector matrix) 
        matrix 
        (M.rowsi alphacell))
      M.zero alphas in
  unified 

(*let find_equiv_class_element morphism s row =
  let s' = unify s in
  let (v, m) = M.pivot row s' in
  match BatEnum.get (V.enum v) with
  | Some (scalar, dim) -> dim
  | None -> assert false
*)

let post_map srk tr_symbols =
  List.fold_left
    (fun map (sym, sym') -> Symbol.Map.add sym (mk_const srk sym') map)
    Symbol.Map.empty
    tr_symbols

let preify srk tr_symbols = substitute_map srk (post_map srk (List.map (fun (x, x') -> (x', x)) tr_symbols))
 

let create_exp_vars srk num_cells num_rows num_trans =
  let rec create_k_ints k vars equiv_num =
    begin match k <= 0 with
      | true -> vars
      | false -> create_k_ints (k - 1) ((mk_symbol srk ~name:("K"^equiv_num^","^(string_of_int k))`TyInt) :: vars) equiv_num
    end
  in
  let rec helper num_cells num_rows kvars svars rvars =
    match num_cells <= 0, num_rows <= 0 with
    | true, true -> kvars, svars, rvars
    | false, false -> 
      let kvars = (create_k_ints num_trans [] (string_of_int num_cells)) :: kvars in
      let rvars = (mk_symbol srk ~name:("R"^(string_of_int num_cells)) `TyInt) :: rvars in
      let svars = (mk_symbol srk ~name:("S"^(string_of_int num_rows)) `TyReal) :: svars in
      helper (num_cells - 1) (num_rows - 1) kvars svars rvars
    | true, false ->
      let svars = (mk_symbol srk `TyReal) :: svars in
      helper num_cells (num_rows - 1) kvars svars rvars
    | false, true -> assert false
  in
  helper num_cells num_rows [] [] []

let create_exp_positive_reqs srk kvarst =
  mk_and srk (List.map (fun var -> 
      mk_leq srk (mk_zero srk) var) 
      (List.flatten kvarst))

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

let all_pairs_kvarst_rvarst kvarst (rvarst : 'a Syntax.term list) =
  let rec helper1 (stack1, r1) kvarst' rvarst' =
    begin match kvarst', rvarst' with
    | [], [] -> []
    | khd :: ktl, rhd :: rtl -> 
        (stack1, r1, khd, rhd) :: (helper1 (stack1, r1) ktl rtl)
    | _ -> assert false
    end
  in
  let rec helper2 kvarst rvarst =
    match kvarst, rvarst with
    | [], [] -> []
    | khd :: khdd :: ktl, rhd :: rhdd :: rtl ->
        (helper1 (khd, rhd) (khdd :: ktl) (rhdd :: rtl)) :: (helper2 (khdd :: ktl) (rhdd :: rtl))
    | khd :: ktl, rhd :: rtl -> []
    | _ -> assert false
  in
  List.flatten (helper2 kvarst rvarst)

let exp_perm_constraints srk krpairs =
  mk_and srk
    (List.map 
      (fun (k1, r1, k2, r2) -> 
        let lessthan k1 k2 = mk_and srk 
          (List.map2 (fun k1' k2' ->
            mk_leq srk k1' k2') k1 k2)
        in
        mk_or srk [lessthan k1 k2;  lessthan k2 k1])
      krpairs)

let exp_equality_k_constraints srk krpairs =
  mk_and srk
    (List.map
      (fun (k1, r1, k2, r2) ->
        mk_iff srk
          (mk_eq srk
            (mk_add srk k1)
            (mk_add srk k2))
          (mk_eq srk r1 r2))
      krpairs)

let exp_other_reset srk kvarst kstack trans_num =
  mk_and srk
    (List.map (fun kstack' ->
      (mk_if srk
        (mk_lt srk
          (mk_add srk kstack)
          (mk_add srk kstack'))
        (mk_leq srk
          (mk_one srk)
          (List.nth kstack' trans_num))))
    kvarst)

let exp_sx_constraints_helper srk ri kstack svarstdims transformers kvarst unialpha tr_symbols =
  let compute_single_svars svart dim  =
    mk_or srk
      ((mk_and srk
        [(mk_eq srk svart (preify srk tr_symbols (Linear.of_linterm srk (M.row dim unialpha)))); (*pivot or row? need to make sure alpha and dim both indexed same *)
         (mk_eq srk ri (mk_real srk (QQ.of_int (-1))))]) ::
      (BatList.of_enum (BatEnum.mapi 
       (fun ind {a; b} ->
         if ZZ.equal (Z.coeff dim a) ZZ.one 
         then (mk_false srk)
         else 
           mk_and srk
           [(mk_eq srk svart (mk_real srk (V.coeff dim b)));
           exp_other_reset srk kvarst kstack ind;
           (mk_eq srk ri (mk_real srk (QQ.of_int ind)))])
       (TSet.enum transformers))))
    in
  mk_and srk (List.map (fun (svar,dim) -> compute_single_svars svar dim) svarstdims)

let exp_sx_constraints srk equiv_pairs transformers kvarst unialpha tr_symbols =
  mk_and srk
    (List.map (fun (kstack, svarstdims, ri) ->
      exp_sx_constraints_helper srk ri kstack svarstdims transformers kvarst unialpha tr_symbols)
    equiv_pairs)


let form_equiv_pairs srk kvarst svarst rvarst =
  List.mapi (fun ind kvar -> (kvar, [(List.nth svarst ind, ind)], List.nth rvarst ind)) kvarst

let exp_lin_term_trans_constraints srk equiv_pairs transformers unialpha =
  mk_and srk
    (List.map (fun (kstack, svarstdims, ri) ->
      mk_and srk (* the lack of or worries me a bit here *)
        (List.map (fun (svar, dim) ->
          mk_eq srk
            (Linear.of_linterm srk (M.row dim unialpha))
            (mk_add srk
              (svar :: 
              (BatList.of_enum (BatEnum.mapi
                (fun ind {a; b} ->
                  mk_mul srk [(List.nth kstack ind); mk_real srk (V.coeff dim b)])
                (TSet.enum transformers))))))
        svarstdims))
    equiv_pairs)

let exp_k_zero_on_reset srk equiv_pairs transformers =
  mk_and srk
    (List.map (fun (kstack, svarstdims, ri) ->
      let (svar, dim) = List.hd svarstdims in
      mk_and srk
       (BatList.of_enum (BatEnum.mapi
         (fun ind {a; b} ->
           if ZZ.equal (Z.coeff dim a) ZZ.zero then (mk_eq srk (List.nth kstack ind) (mk_zero srk))
           else mk_true srk)
         (TSet.enum transformers))))
    equiv_pairs)

let exp srk tr_symbols loop_counter vabs =
  time "ENTERED EXP";
  match vabs with
  | Top -> mk_true srk
  | Bottom -> mk_false srk
  | Vas {v; alphas} -> 
    let num_rows = List.fold_left (fun acc alpha -> (M.nb_rows alpha) + acc) 0 alphas in
    let num_cells = num_rows in
    let num_trans = TSet.cardinal v in
    let kvars, svars, rvars = create_exp_vars srk num_cells num_rows num_trans in
    let map_terms = List.map (fun (var : Syntax.symbol) -> mk_const srk var) in
    let kvarst : 'a Syntax.term list list  = List.map (fun listvars -> map_terms listvars) kvars in
    let svarst, rvarst  = map_terms svars, map_terms rvars in
    let pos_constraints = create_exp_positive_reqs srk ([loop_counter] :: kvarst) in
    let full_trans_constraints = exp_full_transitions_reqs srk kvarst rvarst loop_counter in
    let krpairs : ('a Syntax.term list * 'a Syntax.term * 'a Syntax.term list * 'a Syntax.term) list = 
      all_pairs_kvarst_rvarst kvarst rvarst in
    let perm_constraints = exp_perm_constraints srk krpairs in
    let reset_together_constraints = exp_equality_k_constraints srk krpairs in
    let equiv_pairs = form_equiv_pairs srk kvarst svarst rvarst in
    let sx_constraints = exp_sx_constraints srk equiv_pairs v kvarst (unify alphas) tr_symbols in
    let base_constraints = exp_lin_term_trans_constraints srk equiv_pairs v (unify alphas) in
    let eq_zero_constraints = exp_k_zero_on_reset srk equiv_pairs v in
    let form = 
      mk_and srk [pos_constraints; full_trans_constraints; perm_constraints;
                  reset_together_constraints; sx_constraints; base_constraints; eq_zero_constraints] in
    Log.errorf " Current D VAL %a" (Formula.pp srk) form;
    time "LEFT EXP";
    form


let push_rows matrix first_row =
  BatEnum.fold 
    (fun matrix (dim', row) ->  M.add_row (dim' + first_row) row matrix) 
    M.zero 
    (M.rowsi matrix)

let coproduct srk vabs1 vabs2 : 'a t =
  match vabs1, vabs2 with
  | Top, _ | _, Top -> Top
  | Bottom, vabs2 -> vabs2
  | vabs1, Bottom -> vabs1
  | Vas vabs1, Vas vabs2 ->
    let (v1, v2, alpha1, alpha2) = (vabs1.v, vabs2.v, vabs1.alphas, vabs2.alphas) in
    let push_counter_1 = ref 0 in
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
    Vas {v; alphas}



let gamma srk vas tr_symbols : 'a formula =
  match vas with
  | Bottom -> mk_false srk
  | Top -> mk_true srk
  | Vas {v; alphas} ->
       let term_list  = List.map (fun matrix -> 
        ((M.rowsi matrix)
         /@ (fun (_, row) -> 
            let term = Linear.of_linterm srk row in
            (preify srk tr_symbols term, term)))
        |> BatList.of_enum)
        alphas
        |> List.flatten
    in
   let gamma_transformer t : 'a formula =
     BatList.mapi (fun ind (pre_term, post_term) -> 
         mk_eq srk 
           post_term 
           (mk_add srk [(mk_mul srk [pre_term; mk_real srk (QQ.of_zz (Z.coeff ind t.a))]);
                       mk_real srk (V.coeff ind t.b)]))
       term_list
     |> mk_and srk
    in
    mk_or srk (List.map gamma_transformer (TSet.elements v))



let abstract ?(exists=fun x -> true) (srk : 'a context) (symbols : (symbol * symbol) list) (body : 'a formula)  =
  time "START OF ABSTRACT FUNCTION";
  let body = (rewrite srk ~down:(nnf_rewriter srk) body) in
  let (x''s, x''_forms) = 
    List.split (List.fold_left (fun acc (x, x') -> 
        let x'' = (mk_symbol srk `TyReal) in
        let x''_form = (mk_eq srk (mk_const srk x'') 
                          (mk_sub srk (mk_const srk x') (mk_const srk x))) in
        ((x'', x'), x''_form) :: acc) [] symbols) in
  let postify = substitute_map srk (post_map srk x''s) in
  let alpha_hat (imp : 'a formula) = 
    let r = H.affine_hull srk imp (List.map (fun (x, x') -> x') symbols) in
    let i' = H.affine_hull srk (mk_and srk (imp :: x''_forms)) (List.map (fun (x'', x') -> x'') x''s) in
    let i = List.map postify i' in
    let add_dim m b a term a' offset =
      let (b', v) = V.pivot (Linear.const_dim) (Linear.linterm_of srk term) in
      (M.add_row ((*offset +*) (M.nb_rows m)) v m, V.add_term (QQ.negate b') (offset + (M.nb_rows m)) b, Z.add_term a' (offset + (M.nb_rows m)) a)
    in
    let f t offset = List.fold_left (fun (m, b, a) ele -> add_dim m b a ele t offset) in
    let (mi,b,a) = f ZZ.one 0 (M.zero, V.zero, Z.zero) i in
    let (mr, b, a) = f ZZ.zero (M.nb_rows mi) (M.zero, b, a) r in
    match M.equal mi (M.zero), M.equal mr (M.zero) with
    | true, true -> Top
    | false, true -> Vas {v=TSet.singleton {a;b}; alphas=[mi]}
    | true, false ->  Vas {v=TSet.singleton {a;b}; alphas=[mr]} 
    | false, false -> Vas {v=TSet.singleton {a;b}; alphas=[mi;mr]} (* Matrix 1 row 1 maps to first element a, first elemebt b *)
  in

  let solver = Smt.mk_solver srk in

  let rec go vas count =
    time "ITERATOIN IN LOOP";
    assert (count > 0);
    (*Log.errorf "Current VAS: %a" (Formula.pp srk) (gamma srk vas symbols);
    Log.errorf "___________________________";*)
    Smt.Solver.add solver [mk_not srk (gamma srk vas symbols)];
    match Smt.Solver.get_model solver with
    | `Unsat -> vas
    | `Unknown -> Top
    | `Sat m ->
      match Interpretation.select_implicant m body with
      | None -> assert false
      | Some imp ->
        time "PRE ALPHA";
        let alpha_v = alpha_hat (mk_and srk imp) in
        time "POST ALPHA";
        (*if alpha_v = Top then Top else*)
          go (coproduct srk vas alpha_v) (count - 1)
  in
  Smt.Solver.add solver [body];
  time "START OF MAIN LOOP";
  let result = go Bottom 20 in
  time "END OF MAIN LOOP";
  Log.errorf "Final VAS: %a"  (Formula.pp srk) (gamma srk result symbols);
  time "END OF ABSTRACT FUNCTION";
  result



let join  (srk :'a context) (tr_symbols : (symbol * symbol) list) (vabs1 : 'a t) (vabs2 : 'a t) = assert false
let widen  (srk :'a context) (tr_symbols : (symbol * symbol) list) (vabs1 : 'a t) (vabs2 : 'a t) = assert false
let equal (srk : 'a context) (tr_symbols : (symbol * symbol) list) (vabs1 : 'a t) (vabs2 : 'a t) = assert false

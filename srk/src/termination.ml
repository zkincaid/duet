open Syntax
open BatEnum

module TLLRF = TerminationLLRF
module Vec = Linear.QQVector
module Mat = Linear.QQMatrix
(* module NL = NestedLoops *)

include Log.Make(struct let name = "Termination" end)

type typ_ineq = Tylt0 | Tyeq0 | Tyleq0
  
let getting_vars_after_transition tmul tget_transform s (hd, bd) =
  let hd_then_bd = tmul hd bd in
  let sp = tget_transform s hd in
  let spp = tget_transform s hd_then_bd in
    (sp, spp)


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

(* Map from pre-state vars to their post-state counterparts *)
let post_map tr_symbols =
  List.fold_left
    (fun map (sym, sym') -> Symbol.Map.add sym sym' map)
    Symbol.Map.empty
    tr_symbols

let get_polyhedron_of_formula srk apron_prop cs =
  let srkf = SrkApron.formula_of_property apron_prop in
  let f = match Formula.destruct srk srkf with
    | `And xs -> xs
    | `Tru -> []
    | `Atom _ -> [ srkf ]
    | _ -> SrkApron.pp Format.std_formatter apron_prop ; assert false
  in
  let ppp = Polyhedron.of_implicant ~admit:true cs f in
  let e = Polyhedron.enum ppp in
    BatList.of_enum e
  
let get_coeff_of_symbol cs vec symbol =
  let tid = CoordinateSystem.cs_term_id cs (`App (symbol, [])) in
    let c = Vec.coeff tid vec in
      c

let get_coeffs_from_eq_as_if_leq0 cs eq_t list_symbols =
    BatList.fold_lefti
        (fun existing_coeffs i symbol -> 
          let coeff = get_coeff_of_symbol cs eq_t symbol in
            Vec.add_term coeff i existing_coeffs 
        )
        Vec.zero
        list_symbols

let get_coeff_matrix cs list_symbols constraints =
  BatList.fold_left
    (fun (existing_rows, i) eq -> 
        match eq with
        | `LeqZero t -> 
          begin
            let row = get_coeffs_from_eq_as_if_leq0 cs t list_symbols in
            let m =  Mat.add_row i row existing_rows in
            (m, i+1)
          end
        | `LtZero _ -> Log.error "there should not be strict inequalities"; assert false
        | `EqZero t -> 
          begin
            let row1 = get_coeffs_from_eq_as_if_leq0 cs t list_symbols in
            let m1 = Mat.add_row i row1 existing_rows in
            let row2 = get_coeffs_from_eq_as_if_leq0 cs t list_symbols in
            let neg_row2 = Vec.negate row2 in
            let m = Mat.add_row (i+1) neg_row2 m1 in
            (m, i+2)
          end
    )
    (Mat.zero, 0)
    constraints

let create_const_symbols srk name n = 
  (1 -- n) /@ (fun _ -> mk_const srk (mk_symbol srk ~name:name `TyReal))
  |> BatList.of_enum

let build_formula srk lambdas mat n_rows n_cols op =
  let m = Mat.transpose mat in
  let formulas = ref (mk_true srk) in
  for i = 0 to n_cols-1 do
    let row_i = Mat.row i m in
    (* let k = Linear.term_of_vec srk (List.nth lambdas) row_i in *)
    let lhs = (mk_zero srk) in
    let rlhs = ref lhs in
    for j = 0 to n_rows-1 do
      let ith_ele = Vec.coeff j row_i in
      let term_v = mk_real srk ith_ele in
      let prod = mk_mul srk [ List.nth lambdas j; term_v] in
      let value = mk_add srk [ prod; !rlhs] in
      rlhs := value
    done;
    let lhs_exp = !rlhs in
    let formula = match op with
      | Tyeq0 -> mk_eq srk lhs_exp (mk_zero srk)
      | Tyleq0 -> mk_leq srk lhs_exp (mk_zero srk)
      | Tylt0 -> mk_lt srk lhs_exp (mk_zero srk)
    in
    formulas := mk_and srk [formula; !formulas]
    (* create the list first using map and call mk_and after *)
  done;
  !formulas

let build_lambda_mat_prod_terms srk lambdas mat n_rows n_cols =  
  let m = Mat.transpose mat in
  let r = ref [] in
  for i = 0 to n_cols-1 do
    let row_i = Mat.row i m in
    let lhs = (mk_zero srk) in
    let rlhs = ref lhs in
    for j = 0 to n_rows-1 do
      let ith_ele = Vec.coeff j row_i in
      let term_v = mk_real srk ith_ele in
      let prod = mk_mul srk [ List.nth lambdas j; term_v] in
      let value = mk_add srk [ prod; !rlhs] in
      rlhs := value
    done;
    r := List.concat [!r; [!rlhs]]
  done;
  !r


let build_gt_zero srk lambdas =
  let zero = mk_zero srk in
  List.map (mk_leq srk zero) lambdas
  |> mk_and srk

let build_subtracted_lambdas srk lambdas1 lambdas2 =
  List.map2 (mk_sub srk) lambdas1 lambdas2

let get_constants_vec constraints =
  BatList.fold_left
    (fun (existing_rows, i) eq -> 
        match eq with
        | `LeqZero t -> 
          begin
            let row = Vec.coeff CoordinateSystem.const_id t in
            let neg = QQ.negate row in
            let m =  Vec.add_term neg i existing_rows in
            (m, i+1)
          end
        | `LtZero _ -> failwith "there should not be strict inequalities"
        | `EqZero t -> 
          begin
            let row = Vec.coeff CoordinateSystem.const_id t in
            let neg = QQ.negate row in
            let m =  Vec.add_term neg i existing_rows in
            let row2 = Vec.coeff CoordinateSystem.const_id t in
            let m =  Vec.add_term row2 (i+1) m in
            (m, i+2)
          end
    )
    (Vec.zero, 0)
    constraints
  
let print_formula_to_stdout srk descrip f =
  logf descrip;
  let s2 = (Printf.sprintf "\n%s\n" (Formula.show srk f)) in
  logf "%s" s2;
  ()

let print_ranking_func srk xp_list rf_terms_list rf_delta0 rf_delta interp =
  let rf = List.map
      (fun term -> Interpretation.evaluate_term interp term)
      rf_terms_list
  in
  let d0 = List.map
    (fun term -> Interpretation.evaluate_term interp term)
    rf_delta0
  in
  let d = List.map
    (fun term -> Interpretation.evaluate_term interp term)
    rf_delta
  in
  logf "\n\n********* Ranking function ************\n";
  Format.fprintf Format.std_formatter "f = ";
  let n_cols = List.length rf in
  for i = 0 to n_cols-1 do
    let real_var = List.nth xp_list i in
    pp_symbol srk Format.std_formatter real_var;
    Format.fprintf Format.std_formatter " * ";
    let coe = List.nth rf i in
    QQ.pp Format.std_formatter coe;
    if i < n_cols-1 then
    Format.fprintf Format.std_formatter " + ";
  done;
  
  logf "\nIt has to decrese by this amount in each iter: %a" QQ.pp (QQ.sub QQ.zero (List.nth d 0)); 

  let t = QQ.sub (List.nth d 0) (List.nth d0 0) in 
  logf "\nAnd its lower bound is: %a \n" QQ.pp t;
  logf "\n\n***************************\n\n";
  ()

let prove_termination srk tto_transition_formula loop =
  logf "======= printing poly loop body\n\n";
  let header, body = loop in
  let (_, header_formula) = tto_transition_formula header [] in

  let (xp_xpp, body_formula) = tto_transition_formula body [] in

  let xp_list = List.fold_right (fun (sp, _) l -> sp :: l ) xp_xpp [] in
  let xpp_list = List.fold_right (fun (_, spp) l -> spp :: l ) xp_xpp [] in
  let xp_set = pre_symbols xp_xpp in
  let xpp_set = post_symbols xp_xpp in

  

  let man = Polka.manager_alloc_strict () in
  let header = rewrite srk ~down:(nnf_rewriter srk) header_formula in
  let invariant_prop =
      let exists x =
         (Symbol.Set.mem x xp_set) || (Symbol.Set.mem x xpp_set)
      in
      Abstract.abstract ~exists:exists srk man header
  in
  let invariant_poly = SrkApron.formula_of_property invariant_prop in
    logf "\nInvariant formula:\n%s\n\n"
                        (Formula.show srk invariant_poly);
  let bodyf = rewrite srk ~down:(nnf_rewriter srk) body_formula in
  let bodyf_prop =
      let exists x =
         (Symbol.Set.mem x xp_set) || (Symbol.Set.mem x xpp_set)
      in
      Abstract.abstract ~exists:exists srk man bodyf
  in
  let body_formula = SrkApron.formula_of_property bodyf_prop in
  logf "Loop body formula:\n%s\n\n"
                        (Formula.show srk body_formula);
  let cs = CoordinateSystem.mk_empty srk in
  let header_eqs = get_polyhedron_of_formula srk invariant_prop cs in
  let body_eqs = get_polyhedron_of_formula srk bodyf_prop cs in
  let constraints = BatList.concat [header_eqs; body_eqs] in
  let () = BatList.iter (function
  | `LeqZero t -> logf "%a <= 0" (CoordinateSystem.pp_vector cs) t
  | `LtZero t -> logf "%a < 0" (CoordinateSystem.pp_vector cs) t
  | `EqZero t -> logf "%a = 0" (CoordinateSystem.pp_vector cs) t) constraints
  in
  let mat_a, n_rows = get_coeff_matrix cs xp_list constraints in
  let mat_ap, _ = get_coeff_matrix cs xpp_list constraints in
  let vec_b, _ = get_constants_vec constraints in
  let mat_b = Mat.zero in
  let mat_b = Mat.add_column 0 vec_b mat_b in
  let n_cols = List.length xp_list in
  let lambda1s = create_const_symbols srk "l" n_rows in
  let lambda2s = create_const_symbols srk "r" n_rows in
  let subtractions = build_subtracted_lambdas srk lambda1s lambda2s in
  let l1gt0 = build_gt_zero srk lambda1s in
  print_formula_to_stdout srk "\nConstraints lambda_1 >= 0:\n" l1gt0;
  let l2gt0 = build_gt_zero srk lambda2s in
  print_formula_to_stdout srk "\nConstraints lambda_2 >= 0:\n" l2gt0;
  let eq1 = build_formula srk lambda1s mat_ap n_rows n_cols Tyeq0 in
  print_formula_to_stdout srk "\nConstraints eq1:\n" eq1;
  
  let eq2 = build_formula srk subtractions mat_a n_rows n_cols Tyeq0 in
  print_formula_to_stdout srk "\nConstraints eq2:\n" eq2;

  let eq3 = build_formula srk lambda2s (Mat.add mat_a mat_ap) n_rows n_cols Tyeq0 in
  print_formula_to_stdout srk "\nConstraints eq3:\n" eq3;

  let eq4 = build_formula srk lambda2s mat_b n_rows 1 Tylt0 in
  print_formula_to_stdout srk "\nConstraints eq4:\n" eq4;

  let all_eqs = mk_and srk [l1gt0; l2gt0; eq1; eq2; eq3; eq4] in
  let rf_terms_list = build_lambda_mat_prod_terms srk lambda2s mat_ap n_rows n_cols in
  let rf_delta0 = build_lambda_mat_prod_terms srk lambda1s mat_b n_rows 1 in
  let rf_delta = build_lambda_mat_prod_terms srk lambda2s mat_b n_rows 1 in
  
  match Smt.get_model srk all_eqs with
  | `Sat interp -> 
    logf ~attributes:[`Bold; `Green] "\n\n\nSatisfiable, linear ranking function exists!!!\n\n";
    print_ranking_func srk xp_list rf_terms_list rf_delta0 rf_delta interp;
    
    ()
  | `Unknown ->  (logf ~attributes:[`Bold; `Yellow] "unable to prove linear rf exists or not");()
  | `Unsat -> (logf ~attributes:[`Bold; `Red] "linear ranking function does not exist"); ()


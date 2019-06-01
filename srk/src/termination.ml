open Abstract
open Syntax
open SrkApron
(* open Test_pervasives *)
open Printf
 module Vec = Linear.QQVector
 module Mat = Linear.QQMatrix

include Log.Make(struct let name = "Termination" end)

(* module CRA = Cra *)
(* module T = Cra.K *)
(* module CtxM = Cra.Ctx *)
(* module WG = WeightedGraph *)
module NL = NestedLoops

(* module Ctx = CRA.Ctx *)

(* let srk = Ctx.context *)

let rec print_final_results tshow loops =
  if List.length loops > 0 then printf "\n\n\n=========== Showing final results ==========\n\n\n";
  List.iter 
    (fun loop ->
        NL.print_loop loop;
        printf "path to header: %s\n" (tshow loop.NL.header_f);
        printf "loop body: %s\n" (tshow loop.NL.body_f);
        print_final_results tshow loop.NL.children
    )
    loops

let print_flattened_results tshow loops =
printf "\n\n\n********* Printing flattened loops **********\n\n\n";
 List.iteri
  (fun i (header_f, body_f) -> 
    printf "%d-th loop:\n" i;
    printf "path to header: %s\n" (tshow header_f);
    printf "loop body: %s\n" (tshow body_f);
  )
  loops
  
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
    | `Atom t -> [ srkf ]
    | _ -> SrkApron.pp Format.std_formatter apron_prop ; assert false
  in
  let ppp = Polyhedron.of_implicant ~admit:true cs f in
  let e = Polyhedron.enum ppp in
    BatList.of_enum e
  
let get_coeff_of_symbol cs vec symbol =
   (* Format.fprintf Format.std_formatter "\nExamining this vector:\n"; 
   CoordinateSystem.pp_vector cs Format.std_formatter vec; 
   Format.fprintf Format.std_formatter "\nLooking for id of symbol:\n"; 
   pp_symbol srk Format.std_formatter symbol;  *)
  let tid = CoordinateSystem.cs_term_id cs (`App (symbol, [])) in
    (* Format.fprintf Format.std_formatter "\nid for this symbol:\n"; 
    Format.fprintf Format.std_formatter "%d\n" tid;  *)
    let c = Vec.coeff tid vec in
       (* QQ.pp Format.std_formatter c;  *)
      c

let get_coeffs_from_eq_as_if_leq0 cs eq_t list_symbols =
   (* Format.fprintf Format.std_formatter "\nGetting row from this vector:\n"; 
   CoordinateSystem.pp_vector cs Format.std_formatter eq_t;  *)
    BatList.fold_lefti
        (fun existing_coeffs i symbol -> 
             (* Format.fprintf Format.std_formatter "\nFor %d-th symbol:\n" i; 
             pp_symbol srk Format.std_formatter symbol;  *)
          let coeff = get_coeff_of_symbol cs eq_t symbol in
             (* Format.fprintf Format.std_formatter "\nCoeff for this symbol:\n"; 
             QQ.pp Format.std_formatter coeff;  *)
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
        | `LtZero t -> Log.error "there should not be strict inequalities"; assert false
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

let rec create_const_symbols srk name n =
  if n = 1 then
    let s = mk_const srk (mk_symbol srk ~name:name `TyReal) in
      [s]
  else
    let s = mk_const srk (mk_symbol srk ~name:name `TyReal) in
      s :: create_const_symbols srk name (n-1)

let build_formula srk lambdas mat n_rows n_cols op =
  let m = Mat.transpose mat in
  let formulas = ref (mk_true srk) in
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
    let lhs_exp = !rlhs in
    let formula = match op with
    | "eq_0" -> mk_eq srk lhs_exp (mk_zero srk)
    | "leq_0" -> mk_leq srk lhs_exp (mk_zero srk)
    | "lt_0" -> mk_lt srk lhs_exp (mk_zero srk)
    | _ -> assert false
    in
    formulas := mk_and srk [formula; !formulas]
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
  List.fold_left
    (fun f lambda ->
      mk_and srk [f; mk_leq srk (mk_zero srk) lambda]
    )
    (mk_true srk)
    lambdas

let rec build_subtracted_lambdas srk lambdas1 lambdas2 =
  match lambdas1, lambdas2 with
  | h1 :: t1, h2 :: t2 -> 
    mk_sub srk h1 h2 :: build_subtracted_lambdas srk t1 t2
  | [], [] -> []
  | _, _ -> assert false

let get_constants_vec cs constraints =
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
        | `LtZero t -> Log.error "there should not be strict inequalities"; assert false
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

let print_ranking_func srk cs xp_list rf_terms_list rf_delta0 rf_delta interp =
  (* let len = List.length xp_list in *)
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
    (* let xp = List.nth xp_list i in *)
    pp_symbol srk Format.std_formatter real_var;
    Format.fprintf Format.std_formatter " * ";
    let coe = List.nth rf i in
    QQ.pp Format.std_formatter coe;
    if i < n_cols-1 then
    Format.fprintf Format.std_formatter " + ";
  done;
  
  logf "\nIt has to decrese by this amount in each iter: %a" QQ.pp (QQ.sub QQ.zero (List.nth d 0)); 

  (* let t = QQ.negate (List.nth d0 0) in *)
  let t = QQ.sub (List.nth d 0) (List.nth d0 0) in 
  logf "\nAnd its lower bound is: %a \n" QQ.pp t;
  logf "\n\n***************************\n\n";
  ()

let prove_termination srk tto_transition_formula tmul loop =
  logf "======= printing poly loop body\n\n";
  (* x -> header -> xp -> body -> xpp *)
  let header, body = loop in
  let (x_xp, header_formula) = tto_transition_formula header [] in
  (* let (x_xpp, _) = tto_transition_formula (tmul header body) in *)
  (* let xp_list_from_header = List.fold_right (fun (sp, spp) l -> spp :: l ) x_xp [] in *)

  let (xp_xpp, body_formula) = tto_transition_formula body [] in

  (* let (xp_xpp, body_formula) = T.to_transition_formula body in *)
  let xp_list = List.fold_right (fun (sp, spp) l -> sp :: l ) xp_xpp [] in
  let xpp_list = List.fold_right (fun (sp, spp) l -> spp :: l ) xp_xpp [] in
  (* let x_set = pre_symbols x_xp in *)
  let xp_set = pre_symbols xp_xpp in
  (* let xp_set = Symbol.Set.inter (post_symbols x_xp) (pre_symbols xp_xpp) in *)
  let xpp_set = post_symbols xp_xpp in
  (* Format.fprintf Format.std_formatter "\nx_set:\n"; *)

  
  (* Format.fprintf Format.std_formatter "\nxp_set:\n";
   let () = Symbol.Set.iter
    (fun s -> pp_symbol srk Format.std_formatter s)
    xp_set
  in
  Format.fprintf Format.std_formatter "\nxpp_set:\n";
   let () = Symbol.Set.iter
    (fun s -> pp_symbol srk Format.std_formatter s)
    xpp_set
  in
  Format.fprintf Format.std_formatter "\n\n"; *)

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
  List.iter
    (fun (xp) -> 
      try let tid = (CoordinateSystem.cs_term_id cs (`App (xp, []))) in
        ()
      with Not_found -> CoordinateSystem.admit_cs_term cs (`App (xp, [])); ();
    )
    xp_list;
  List.iter
    (fun (xpp) -> 
      try let tid = (CoordinateSystem.cs_term_id cs (`App (xpp, []))) in
        ()
      with Not_found -> CoordinateSystem.admit_cs_term cs (`App (xpp, [])); ();
    )
    xpp_list;
  (* List.iter
    (fun (xp) -> 
      let tid = (CoordinateSystem.cs_term_id cs (`App (xp, []))) in
      pp_symbol srk Format.std_formatter xp;
        Format.fprintf Format.std_formatter " -> %d:\n" tid;
    )
    xp_list;
  List.iter
    (fun (xpp) -> 
      let tid = (CoordinateSystem.cs_term_id cs (`App (xpp, []))) in
      pp_symbol srk Format.std_formatter xpp;
        Format.fprintf Format.std_formatter " -> %d:\n" tid;
    )
    xpp_list; *)
  (* let () = BatList.iter (function
  | `LeqZero t -> Log.errorf "%a <= 0" (CoordinateSystem.pp_vector cs) t
  | `LtZero t -> Log.errorf "%a < 0" (CoordinateSystem.pp_vector cs) t
  | `EqZero t -> Log.errorf "%a = 0" (CoordinateSystem.pp_vector cs) t) header_eqs
  in *)
  (* let () = BatList.iter (function
  | `LeqZero t -> Log.errorf "%a <= 0" (CoordinateSystem.pp_vector cs) t
  | `LtZero t -> Log.errorf "%a < 0" (CoordinateSystem.pp_vector cs) t
  | `EqZero t -> Log.errorf "%a = 0" (CoordinateSystem.pp_vector cs) t) body_eqs
  in *)
  let constraints = BatList.concat [header_eqs; body_eqs] in
  let () = BatList.iter (function
  | `LeqZero t -> logf "%a <= 0" (CoordinateSystem.pp_vector cs) t
  | `LtZero t -> logf "%a < 0" (CoordinateSystem.pp_vector cs) t
  | `EqZero t -> logf "%a = 0" (CoordinateSystem.pp_vector cs) t) constraints
  in
  let mat_a, n_rows = get_coeff_matrix cs xp_list constraints in
  let mat_ap, n_rows2 = get_coeff_matrix cs xpp_list constraints in
  let vec_b, n_rows3 = get_constants_vec cs constraints in
  let mat_b = Mat.zero in
  let mat_b = Mat.add_column 0 vec_b mat_b in
    (* Format.fprintf Format.std_formatter "\nMatrix A:\n";
    (Mat.pp Format.std_formatter mat_a);
    Format.fprintf Format.std_formatter "\nMatrix A':\n";
    (Mat.pp Format.std_formatter mat_ap);
    Format.fprintf Format.std_formatter "\nMatrix b:\n";
    (Mat.pp Format.std_formatter mat_b); *)
  let n_cols = List.length xp_list in
  let lambda1s = create_const_symbols srk "l" n_rows in
  let lambda2s = create_const_symbols srk "r" n_rows in
  let subtractions = build_subtracted_lambdas srk lambda1s lambda2s in
  let l1gt0 = build_gt_zero srk lambda1s in
  print_formula_to_stdout srk "\nConstraints lambda_1 >= 0:\n" l1gt0;
  let l2gt0 = build_gt_zero srk lambda2s in
  print_formula_to_stdout srk "\nConstraints lambda_2 >= 0:\n" l2gt0;
  let eq1 = build_formula srk lambda1s mat_ap n_rows n_cols "eq_0" in
  print_formula_to_stdout srk "\nConstraints eq1:\n" eq1;
  
  let eq2 = build_formula srk subtractions mat_a n_rows n_cols "eq_0" in
  print_formula_to_stdout srk "\nConstraints eq2:\n" eq2;

  let eq3 = build_formula srk lambda2s (Mat.add mat_a mat_ap) n_rows n_cols "eq_0" in
  print_formula_to_stdout srk "\nConstraints eq3:\n" eq3;

  let eq4 = build_formula srk lambda2s mat_b n_rows 1 "lt_0" in
  print_formula_to_stdout srk "\nConstraints eq4:\n" eq4;

  let all_eqs = mk_and srk [l1gt0; l2gt0; eq1; eq2; eq3; eq4] in
  let rf_terms_list = build_lambda_mat_prod_terms srk lambda2s mat_ap n_rows n_cols in
  (* List.iter (fun x -> Syntax.Term.pp srk Format.std_formatter x; Format.fprintf Format.std_formatter "\n" ) rf_terms_list; *)
  let rf_delta0 = build_lambda_mat_prod_terms srk lambda1s mat_b n_rows 1 in
  let rf_delta = build_lambda_mat_prod_terms srk lambda2s mat_b n_rows 1 in
  (* let solver = SrkZ3.mk_solver srk in
  SrkZ3.Solver.add solver [all_eqs]; *)
  match Smt.get_model srk all_eqs with
  | `Sat interp -> 
    logf ~attributes:[`Bold; `Green] "\n\n\nSatisfiable, linear ranking function exists!!!\n\n";
    (* List.iter (fun x -> pp_symbol srk Format.std_formatter x; ) xp_list; *)
    print_ranking_func srk cs xp_list rf_terms_list rf_delta0 rf_delta interp;
    (* List.map
      (fun term -> 
        Format.fprintf Format.std_formatter "\nlambda_1s are: ";
        let t = Interpretation.evaluate_term interp term in
          QQ.pp Format.std_formatter t;
        
        )
      lambda1s;
    List.map
      (fun term -> 
        Format.fprintf Format.std_formatter "\nlambda_2s are: ";
        let t = Interpretation.evaluate_term interp term in
          QQ.pp Format.std_formatter t;
        )
      lambda2s; *)
    ()
  | `Unknown ->  (logf ~attributes:[`Bold; `Yellow] "unable to prove linear rf exists or not");()
  | `Unsat -> (logf ~attributes:[`Bold; `Red] "linear ranking function does not exist"); ()

let prove_termination_of_loops srk tto_transition_formula tmul loops =
  List.iter
    (fun loop -> prove_termination srk tto_transition_formula tmul loop)
    loops
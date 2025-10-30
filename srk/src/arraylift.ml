open Syntax
open Iteration

let rec quantified_substitution (srk : 'a context) (f : 'a formula) (sub : int -> int) (qo : int) : 'a formula = 
  match Formula.destruct srk f with 
  | `Tru | `Fls -> f
  | `And ls -> mk_and srk (List.map (fun f -> quantified_substitution srk f sub qo) ls)
  | `Or ls -> mk_or srk (List.map (fun f -> quantified_substitution srk f sub qo) ls)
  | `Not f' -> mk_not srk (quantified_substitution srk f' sub qo)
  | `Quantify (`Exists, name, t, body) ->
    mk_exists srk ~name t (quantified_substitution srk body sub (qo + 1))
  | `Quantify (`Forall, name, t, body) ->
    mk_forall srk ~name t (quantified_substitution srk body sub (qo + 1))
  | `Atom _ | `Proposition _ ->
    let rep = substitute srk (fun (i, t) -> if i < qo then mk_var srk i t else mk_var srk ((sub (i - qo)) + qo) t) f in 
    (* print_string "Replacing quantified formula:\n"; print_string (Formula.show srk f); print_string "\n with \n"; print_string (Formula.show srk rep); print_newline (); *)
    rep
  | `Ite (f, l, r) -> 
    mk_ite srk (quantified_substitution srk f sub qo) 
      (quantified_substitution srk l sub qo) 
      (quantified_substitution srk r sub qo)

let rec quantified_substitution_expr (srk : 'a context) (f : 'a formula) (index : int) (e : ('a, typ_fo) expr) : 'a formula = 
  match Formula.destruct srk f with 
  | `Tru | `Fls -> f
  | `And ls -> mk_and srk (List.map (fun f -> quantified_substitution_expr srk f index e) ls)
  | `Or ls -> mk_or srk (List.map (fun f -> quantified_substitution_expr srk f index e) ls)
  | `Not f' -> mk_not srk (quantified_substitution_expr srk f' index e)
  | `Quantify (`Exists, name, t, body) ->
    mk_exists srk ~name t (quantified_substitution_expr srk body (index + 1) e)
  | `Quantify (`Forall, name, t, body) ->
    mk_forall srk ~name t (quantified_substitution_expr srk body (index + 1) e)
  | `Atom _ | `Proposition _ ->
    let rep = substitute srk (fun (i, t) -> if i = index then e else mk_var srk i t) f in rep
  | `Ite (f, l, r) -> 
    mk_ite srk (quantified_substitution_expr srk f index e) 
      (quantified_substitution_expr srk l index e) 
      (quantified_substitution_expr srk r index e)



let reverse_skolem (srk : 'a context) (f : 'a formula) (array_bruijn : int) : (string * typ_fo) list * 'a formula = 
  print_string "Reversing skolemization of formula:\n"; print_string (Formula.show srk f); print_string "\n with array bruijn index "; print_int array_bruijn; print_newline ();
  let rec could_be_array (t : 'a arr_term) (qo : int) : bool = 
    match ArrTerm.destruct srk t with 
    | `Var (index, _) -> index = array_bruijn + qo 
    | `Ite (_, l, r) -> (could_be_array l qo) || (could_be_array r qo)
    | `Store (a, _, _) -> (could_be_array a qo)
    | `App _ -> false
  in

  let rec collect_accesses_formula (f : 'a formula) (acc : int list) (qo : int) : int list = 
    match Formula.destruct srk f with 
    | `Atom (`ArrEq _) -> failwith "Array equalities should not appear in Skolem fragment"
    | `Atom (`Arith (_, t1, t2)) -> collect_accesses_arith t1 (collect_accesses_arith t2 acc qo) qo
    | `Atom (`IsInt t) -> collect_accesses_arith t acc qo
    | `Tru | `Fls | `Proposition _ -> acc
    | `And ls | `Or ls -> List.fold_left (fun a f -> collect_accesses_formula f a qo) acc ls
    | `Not _ -> failwith "Not is not supported in Skolem fragment"
    | `Quantify (_, _, _, f) -> collect_accesses_formula f acc (qo + 1)
    | `Ite (f, l, r) -> collect_accesses_formula f (collect_accesses_formula l (collect_accesses_formula r acc qo) qo) qo
  and collect_accesses_arith (t : 'a arith_term) (acc : int list) (qo : int): int list = 
    match ArithTerm.destruct srk t with 
    | `Real _ | `App _ | `Var _ -> acc
    | `Add ls | `Mul ls -> List.fold_left (fun a t -> collect_accesses_arith t a qo) acc ls
    | `Binop (_, t1, t2) -> collect_accesses_arith t1 (collect_accesses_arith t2 acc qo) qo
    | `Unop (_, t) -> collect_accesses_arith t acc qo
    | `Ite (f, l, r) -> collect_accesses_formula f (collect_accesses_arith l (collect_accesses_arith r acc qo) qo) qo
    | `Select (arr, index) -> (if could_be_array arr qo then ( 
      match ArithTerm.destruct srk index with 
        | `Var (v, _) -> if List.mem (v - qo) acc then acc else (v - qo) :: acc
        | _ -> failwith "Array index should be a variable"
    ) else acc)
    in
    let accesses = collect_accesses_formula (rewrite srk ~down:(pos_rewriter srk) f) [] 0 in 
    let replacements = List.mapi (fun i access -> (access, i + 1)) accesses in
    print_string "Collected accesses at variables: "; 
    List.iter (fun (a, _) -> print_int a; print_string " ") replacements; print_newline ();

    let f = quantified_substitution srk f (fun i -> if i = 0 then i else i + List.length replacements) 0 in
    let array_bruijn = array_bruijn + List.length replacements in
    let replacements = List.map (fun (a, r) -> if a = 0 then (a, r) else (a + List.length replacements, r)) replacements in 

    print_string "After adjusting for new quantifiers:\n"; print_string (Formula.show srk f); print_newline ();
    print_string "Array Bruijn is now "; print_int array_bruijn; print_newline ();
    print_string "Replacements are: ";
    List.iter (fun (a, r) -> print_string ("(" ^ string_of_int a ^ " -> " ^ string_of_int r ^ ") ")) replacements; print_newline ();
    
    let rec replace_access (a : 'a arr_term) (index : 'a arith_term) (qo : int) : 'a arith_term = 
      match ArrTerm.destruct srk a with 
      | `Var (v, _) -> if (v - qo) = array_bruijn then (
        match ArithTerm.destruct srk index with 
          | `Var (vind, _) -> (mk_var srk (snd (List.find (fun (access, _) -> access = (vind - qo)) replacements) + qo) `TyInt)
          | _ -> failwith "Array index should be a variable"
      ) else mk_select srk a index
      | `Ite (f, l, r) -> (mk_ite srk f (replace_access l index qo) (replace_access r index qo))
      | `Store (a, store_index, value) -> (
          let ae = replace_access a index qo in
          mk_ite srk (mk_eq srk store_index index) value ae
      )
      | `App (_, _) -> failwith "Array applications not supported"
    in

  let arith_term_rewriter (qo : int) (a : 'a arith_term) : 'a arith_term = 
    let rewriter a = 
      match Expr.refine srk a with 
      | `Formula _ | `ArrTerm _-> a
      | `ArithTerm at -> (
        match ArithTerm.destruct srk at with
          | `Select (arr, index) -> ((replace_access arr index qo) :> (('a, typ_fo) expr))
          | _ -> (at :> (('a, typ_fo) expr)))
    in
    rewrite srk ~down:rewriter a
  in
  let rec eliminate_arrays (f : 'a formula) (qo : int) : 'a formula = 
    match Formula.destruct srk f with 
    | `Atom (`ArrEq _) -> failwith "Array equalities should not appear in Skolem fragment"
    | `Atom (`Arith (`Eq, t1, t2)) -> mk_eq srk (arith_term_rewriter qo t1) (arith_term_rewriter qo t2)
    | `Atom (`Arith (`Leq, t1, t2)) -> mk_leq srk (arith_term_rewriter qo t1) (arith_term_rewriter qo t2)
    | `Atom (`Arith (`Lt, t1, t2)) -> mk_lt srk (arith_term_rewriter qo t1) (arith_term_rewriter qo t2)
    | `Atom (`IsInt t) -> mk_is_int srk (arith_term_rewriter qo t)
    | `Tru | `Fls | `Proposition _ -> f
    | `And ls -> mk_and srk (List.map (fun f -> eliminate_arrays f qo) ls)
    | `Or ls -> mk_or srk (List.map (fun f -> eliminate_arrays f qo) ls)
    | `Not _ -> failwith "Not is not supported in Skolem fragment"
    | `Quantify (`Exists, name, t, body) ->
      mk_exists srk ~name t (eliminate_arrays body (qo + 1))
    | `Quantify (`Forall, name, t, body) ->
      mk_forall srk ~name t (eliminate_arrays body (qo + 1))  
    | `Ite (f, l, r) -> 
      mk_ite srk (eliminate_arrays f qo) (eliminate_arrays l qo) (eliminate_arrays r qo)
    in

  let f = eliminate_arrays (rewrite srk ~down:(pos_rewriter srk) f) 0 in 
  print_string "After replacing accesses:\n"; print_string (Formula.show srk f); print_newline ();
  let f = quantified_substitution srk f (fun i -> if i > array_bruijn then i else i + 1) 0 in 
  print_string "After shifting quantifiers:\n"; print_string (Formula.show srk f); print_newline ();
  let fc = List.map (fun (access, replacement) -> 
    mk_if srk (mk_eq srk (mk_var srk 1 `TyInt) (mk_var srk (if access > array_bruijn then access else access + 1) `TyInt)) (mk_eq srk (mk_var srk 0 `TyInt) (mk_var srk (replacement + 1) `TyInt))) replacements in 
  let f'' = mk_exists srk `TyInt (mk_and srk (f :: fc)) in 
  let existential_vars = List.map (fun (_, replacement) -> ("a" ^ string_of_int replacement, `TyInt)) replacements in
  print_string "Reversed skolemization to :\n"; print_string (Formula.show srk f''); print_newline ();
  print_string "With existential variables : ";
  List.iter (fun (n, _) -> print_string (n ^ " ")) existential_vars;
  existential_vars, f'' 

  

let rec bubble (srk : 'a context) (f : 'a formula) (shift : int): ((string * typ_fo) list * (string * typ_fo) option * 'a formula) = 
  print_string "\nBubbling formula :\n"; print_string (Formula.show srk f); print_string "\n with shift "; print_int shift; print_newline ();
  let (exists, forall, formula) = match Formula.destruct srk f with 
  | `Tru | `Fls -> ([], None, f)
  | `And ls -> 
    let (exists, forall, parts_with_forall, parts_without_forall, _) = List.fold_left 
      (fun (acc_exists, acc_forall, acc_parts_with_forall, acc_parts_without_forall, acc_ctr) f -> 
        let (exists, forall, part) = bubble srk f (shift + acc_ctr) in 
        let acc_exists = acc_exists @ exists in 
        match (forall) with 
        | Some _ -> (acc_exists, forall, part :: acc_parts_with_forall, acc_parts_without_forall, acc_ctr + (List.length exists))
        | None -> (acc_exists, acc_forall, acc_parts_with_forall, part :: acc_parts_without_forall, acc_ctr + (List.length exists))
        )
      ([], None, [], [], 0) ls in 
    (match parts_with_forall with 
      | [] -> (exists, forall, mk_and srk parts_without_forall)
      | _ -> 
        let parts_without_forall = List.map (fun p -> quantified_substitution srk p (fun i -> i + 1) 0) parts_without_forall in 
        (exists, forall, mk_and srk (parts_with_forall @ parts_without_forall)))
  | `Or ls ->
    let (exists, forall, parts_with_forall, parts_without_forall, _) = List.fold_left 
      (fun (acc_exists, acc_forall, acc_parts_with_forall, acc_parts_without_forall, acc_ctr) f ->
        let (exists, forall, part) = bubble srk f (shift + acc_ctr) in 
        let acc_exists = exists @ acc_exists in 
        match forall with 
        | Some _ -> (acc_exists, forall, part :: acc_parts_with_forall, acc_parts_without_forall, acc_ctr + (List.length exists))
        | None -> (acc_exists, acc_forall, acc_parts_with_forall, part :: acc_parts_without_forall, acc_ctr + (List.length exists))
        ) 
      ([], None, [], [], 1) ls in 
      let parts = (match parts_with_forall with
        | [] -> parts_without_forall
        | _ -> parts_with_forall @ (List.map (fun p -> quantified_substitution srk p (fun i -> i + 1) 0) parts_without_forall)) in 
      let branch_variable_number = match forall with | Some _ -> 1 | None -> 0 in 
      let with_branch_formula = mk_or srk (List.mapi (fun i part -> mk_and srk [part; mk_eq srk (mk_var srk branch_variable_number `TyInt) (mk_int srk i)]) parts) in 
      (("branch", `TyInt) :: exists, forall, with_branch_formula)
  | `Not _ -> failwith "Not is not supported in Skolem fragment"
  | `Quantify (`Forall, name, t, body) -> (
    let shifted_body = quantified_substitution srk body (fun i -> if i = 0 then i else i + shift) 0 in 
    (* print_string "Shifted forall body to :\n"; print_string (Formula.show srk shifted_body); print_newline ();
    print_string "Body was:\n"; print_string (Formula.show srk body); print_newline (); *)
    assert (t = `TyInt);
    [], Some (name, t), shifted_body )
  | `Quantify (`Exists, name, typ, body) ->
    let (exists, forall, body') = bubble srk body shift in 
    (* print_newline (); print_string "BODY!\n"; print_string (Formula.show srk body'); print_newline (); *)
    if (typ = `TyArr) 
      then (
        match forall with 
        | None -> failwith "TODO: Should be able to just replace array variable with int"
        | Some _ -> 
          let e, f = reverse_skolem srk body' ((List.length exists) + 1) in 
          (exists @ e, forall, f)
      ) 
      else (exists @ [(name, typ)], forall, body')
  | `Atom _ | `Proposition _ -> 
    ([], None, (substitute srk (fun (i, t) -> if (i = 0) then (mk_var srk i t) else (mk_var srk (i + shift) t)) f))
  | `Ite (f, l, r) -> bubble srk (mk_or srk [mk_and srk [f ; l]; mk_and srk [mk_not srk f; r]]) shift
  in 
  print_string "\nBubbled to :\n"; print_string (Formula.show srk (List.fold_left (fun acc (name, t) -> mk_exists srk ~name t acc) (match forall with | None -> formula | Some (name, t) -> mk_forall srk ~name t formula) exists)); print_newline ();
  (exists, forall, formula)

let array_exponentiate (srk : 'a context) (e : 'a exp_op) : ('a TransitionFormula.t -> 'a Syntax.arith_term -> 'a Syntax.formula) =
  let e' (tf : 'a TransitionFormula.t) (k : 'a arith_term) : ('a formula) = 
    let f =  (TransitionFormula.formula tf)  in 
    let array_symbols = List.filter (fun (s, s') -> typ_symbol srk s = `TyArr && typ_symbol srk s' = `TyArr) (TransitionFormula.symbols tf) in 
    let zs = List.fold_left (fun acc (s, s') -> (s, mk_symbol srk `TyInt) :: (s', mk_symbol srk `TyInt) :: acc) [] array_symbols in 
    let j = mk_symbol srk ~name:"j" `TyInt in 
    let j' = mk_symbol srk ~name:"j'" `TyInt in 
    let projected_formula = mk_and srk (f :: (mk_eq srk (mk_const srk j) (mk_const srk j')) :: (List.map (fun (a, z) -> mk_eq srk (mk_select srk (mk_const srk a) (mk_const srk j)) (mk_const srk z)) zs)) in 
    let projected_formula = List.fold_left (fun acc (s, s') -> mk_exists_const srk s' (mk_exists_const srk s acc)) projected_formula (TransitionFormula.symbols tf) in 
    let projected_formula = mk_exists_const srk j' (mk_exists_const srk j projected_formula) in 
    print_newline (); print_string (Formula.show srk projected_formula); print_newline ();

    let existentials, i, skolemized = bubble srk projected_formula 0 in 
    print_newline (); print_string (Formula.show srk skolemized); print_newline ();
    let with_universal = match i with
    | None -> skolemized
    | Some (name, typ) -> mk_forall srk ~name typ (skolemized) in (* should use Quantifier.qe_mbp to eliminate. *)
    let skolemized_js = quantified_substitution_expr srk with_universal (List.length existentials - 1) (mk_const srk j') in 
    let skolemized_js = quantified_substitution_expr srk skolemized_js (List.length existentials - 2) (mk_const srk j) in 
    let rec drop_2 acc = function | [] | [_] | [_ ; _] -> List.rev acc | x :: xs -> drop_2 (x :: acc) xs in 
    let existentials = drop_2 [] existentials in
    let fully_skolemized = Formula.skolemize_free srk skolemized_js in 



    let to_print = List.fold_left (fun acc (n, t) -> mk_exists srk ~name:n t acc) fully_skolemized existentials in
    let to_print = List.fold_left (fun acc (_, z) -> mk_exists_const srk z acc) to_print zs in 
    print_newline (); print_string (Formula.show srk to_print); print_newline (); 
    (* let with_universal = Formula.skolemize_free srk with_universal in *)
    print_string "\nSkolemized formula before QE:\n"; print_string (Formula.show srk fully_skolemized); print_newline ();
    let eliminated = SrkZ3.qe srk fully_skolemized in 
    print_string "\nEliminated formula:\n"; print_string (Formula.show srk eliminated); print_newline ();
    let tf'_symbols = (j, j') :: List.map (fun (s, s') -> if (typ_symbol srk s = `TyArr) then (((List.find (fun (sym, _) -> sym = s') zs) |> snd), ((List.find (fun (sym, _) -> sym = s') zs) |> snd)) else (s, s')) (TransitionFormula.symbols tf) in 
    let tf' = TransitionFormula.make ~exists:(fun sym -> (not (List.exists (fun (s, s') -> s = sym || s' = sym) tf'_symbols)) && TransitionFormula.exists tf sym) eliminated tf'_symbols in 
    print_string "\nFinal transition formula:\n"; print_string (TransitionFormula.show srk tf'); print_newline ();
    let solver' = Solver.make srk tf' in
    let exponentiated = e solver' k in 
    let ret = substitute_sym srk (fun s ->
      match List.find_opt (fun (_, z) -> s = z) zs with 
        | Some (a, _) -> mk_select srk (mk_const srk a) (mk_const srk j)
        | None -> mk_const srk s
      ) exponentiated in 
    print_string "\nFinal exponentiated formula:\n"; print_string (Formula.show srk ret); print_newline ();
    ret
  in 
  e'
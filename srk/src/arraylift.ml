open Syntax
open Iteration


let reverse_skolem (srk : 'a context) (f : 'a formula) (array_bruijn : int) : (string * typ_fo) list * 'a formula = 
  let rec could_be_array (t : 'a arr_term) : bool = 
    match ArrTerm.destruct srk t with 
    | `Var (index, _) -> index = array_bruijn (*need to add existential depth to check*)
    | `Ite (_, l, r) -> (could_be_array l) || (could_be_array r)
    | `Store (a, _, _) -> (could_be_array a)
    | `App _ -> false
  in

  let rec collect_accesses_formula (f : 'a formula) (acc : int list) : int list = 
    match Formula.destruct srk f with 
    | `Atom (`ArrEq _) -> failwith "Array equalities should not appear in Skolem fragment"
    | `Atom (`Arith (_, t1, t2)) -> collect_accesses_arith t1 (collect_accesses_arith t2 acc)
    | `Atom (`IsInt t) -> collect_accesses_arith t acc
    | `Tru | `Fls | `Proposition _ -> acc
    | `And ls | `Or ls -> List.fold_left (fun a f -> collect_accesses_formula f a) acc ls
    | `Not _ -> failwith "Not is not supported in Skolem fragment"
    | `Quantify _ -> failwith "Quantifiers should have been bubbled out"
    | `Ite (f, l, r) -> collect_accesses_formula f (collect_accesses_formula l (collect_accesses_formula r acc))
  and collect_accesses_arith (t : 'a arith_term) (acc : int list) : int list = 
    match ArithTerm.destruct srk t with 
    | `Real _ | `App _ | `Var _ -> acc
    | `Add ls | `Mul ls -> List.fold_left (fun a t -> collect_accesses_arith t a) acc ls
    | `Binop (_, t1, t2) -> collect_accesses_arith t1 (collect_accesses_arith t2 acc)
    | `Unop (_, t) -> collect_accesses_arith t acc
    | `Ite (f, l, r) -> collect_accesses_formula f (collect_accesses_arith l (collect_accesses_arith r acc))
    | `Select (arr, index) -> (if could_be_array arr then (
      match ArithTerm.destruct srk index with 
        | `Var (v, _) -> if List.mem v acc then acc else v :: acc
        | _ -> failwith "Array index should be a variable"
    ) else acc)
    in
    let accesses = collect_accesses_formula f [] in 
    let replacements = List.mapi (fun i access -> (access, i + array_bruijn)) accesses in 



  let rec access_array_term (a : 'a arr_term) (e : 'a arith_term): 'a arith_term = 
    match ArrTerm.destruct srk a with 
    | `Var (v, _) -> if (v = array_bruijn) then (
        match ArithTerm.destruct srk e with 
        | `Var (ve, _) -> (mk_var srk (snd (List.find (fun (access, _) -> access = ve) replacements)) `TyInt)
        | _ -> failwith "Array index should be a variable"
    ) else mk_select srk a e
    | `Ite (f, l, r) -> (mk_ite srk f (access_array_term l e) (access_array_term r e))
    | `Store (a, index, value) -> (
        let ae = access_array_term a e in
        mk_ite srk (mk_eq srk index e) value ae
    )
    | `App (_, _) -> failwith "Array applications not supported"
  in

  let arith_term_rewriter (a : 'a arith_term) : 'a arith_term = 
    match ArithTerm.destruct srk a with 
    | `Select (arr, index) -> access_array_term arr index
    | _ -> a
  in

  let formula_rewriter f = 
    match (Formula.destruct srk f) with
    | `Atom (`ArrEq _) -> failwith "Array equalities should not appear in Skolem fragment"
    | _ -> f
  in

  let elimination_rewriter (e : ('a, 'b) expr) : ('a, 'b) expr = 
    match Expr.refine srk e with 
    | `ArithTerm t -> ((arith_term_rewriter t) :> (('a, typ_fo) expr)) 
    | `Formula f -> (formula_rewriter f :> (('a, typ_fo) expr))
    | `ArrTerm _ -> failwith "Array terms should be already eliminated on the way down."
  in 

  let f' = rewrite srk ~down:elimination_rewriter f in 
  let shifted_f' = substitute srk (fun (i, t) -> mk_var srk (i + 1) t) f' in 
  let fc = List.map (fun (access, replacement) -> 
    mk_if srk (mk_eq srk (mk_var srk 1 `TyInt) (mk_var srk (access + 1) `TyInt)) (mk_eq srk (mk_var srk 0 `TyInt) (mk_var srk (replacement + 1) `TyInt))) replacements in 
  let f'' = mk_exists srk `TyInt (mk_and srk (shifted_f' :: fc)) in 
  let existential_vars = List.map (fun (_, replacement) -> ("a" ^ string_of_int replacement, `TyInt)) replacements in
  existential_vars, f'' 

  

let rec bubble (srk : 'a context) (f : 'a formula) (shift : int): ((string * typ_fo) list * (string * typ_fo) option * 'a formula) = 
  match Formula.destruct srk f with 
  | `Tru | `Fls -> ([], None, f)
  | `And ls -> 
    let (exists, forall, parts, _) = List.fold_left 
      (fun (acc_exists, acc_forall, acc_parts, acc_ctr) f -> 
        let (exists, forall, part) = bubble srk f (shift + acc_ctr) in 
        let acc_exists = acc_exists @ exists in 
        match (acc_forall) with 
        | Some _ -> (acc_exists, acc_forall, part :: acc_parts, acc_ctr + (List.length exists))
        | None -> (acc_exists, forall, part :: acc_parts, acc_ctr + (List.length exists))
        )
      ([], None, [], 0) ls in 
    (exists, forall, mk_and srk parts)
  | `Or ls ->
    let (exists, forall, parts, _) = List.fold_left 
      (fun (acc_exists, acc_forall, acc_parts, acc_ctr) f ->
        let (exists, forall, part) = bubble srk f (shift + acc_ctr) in 
        let acc_exists = exists @ acc_exists in 
        match acc_forall with 
        | Some _ -> (acc_exists, acc_forall, part :: acc_parts, acc_ctr + (List.length exists))
        | None -> (acc_exists, forall, part :: acc_parts, acc_ctr + (List.length exists))
        ) 
      ([], None, [], 1) ls in 
      let branch_variable_number = match forall with | Some _ -> 1 | None -> 0 in 
      let with_branch_formula = mk_or srk (List.mapi (fun i part -> mk_and srk [part; mk_eq srk (mk_var srk branch_variable_number `TyInt) (mk_int srk i)]) parts) in 
      (("branch", `TyInt) :: exists, forall, with_branch_formula)
  | `Not _ -> failwith "Not is not supported in Skolem fragment"
  | `Quantify (`Forall, name, t, body) ->
    let shifted_body = substitute srk (fun (i, typ) -> if (i = 0) then mk_var srk i typ else mk_var srk (i + shift) typ) body in 
    assert (t = `TyInt);
    [], Some (name, t), shifted_body
  | `Quantify (`Exists, name, typ, body) ->
    let (exists, forall, body') = bubble srk body shift in 
    if (typ = `TyArr) 
      then (
        match forall with 
        | None -> failwith "TODO: Should be able to just replace array variable with int"
        | Some _ -> 
          let e, f = reverse_skolem srk body' (List.length exists) in 
          (exists @ e, forall, f)
      ) 
      else (exists @ [(name, typ)], forall, body')
  | `Atom _ | `Proposition _ -> 
    ([], None, (substitute srk (fun (i, t) -> if (i = 0) then (mk_var srk i t) else (mk_var srk (i + shift) t)) f))
  | `Ite (f, l, r) -> bubble srk (mk_or srk [mk_and srk [f ; l]; mk_and srk [mk_not srk f; r]]) shift

let array_exponentiate (srk : 'a context) (e : 'a exp_op) : ('a exp_op) =
  let e' (s : 'a Solver.t) (k : 'a arith_term) : ('a formula) = 
    let tf = Solver.get_transition_formula s in 
    let f = TransitionFormula.formula tf in 
    let array_symbols = List.filter (fun (s, s') -> typ_symbol srk s = `TyArr && typ_symbol srk s' = `TyArr) (TransitionFormula.symbols tf) in 
    let zs = List.fold_left (fun acc (s, s') -> (s, mk_symbol srk `TyInt) :: (s', mk_symbol srk `TyInt) :: acc) [] array_symbols in 
    let j = mk_symbol srk ~name:"j" `TyInt in
    let j' = mk_symbol srk ~name:"j'" `TyInt in 
    let projected_formula = mk_and srk (f :: (mk_eq srk (mk_const srk j) (mk_const srk j')) :: (List.map (fun (a, z) -> mk_eq srk (mk_select srk (mk_const srk a) (mk_const srk j)) (mk_const srk z)) zs)) in 

    let existentials, i, skolemized = bubble srk projected_formula 0 in 
    let with_universal = match i with
    | None -> skolemized
    | Some (name, typ) -> mk_forall srk ~name typ (skolemized) in (* should use Quantifier.qe_mbp to eliminate. *)
    let eliminated = Quantifier.qe_mbp srk with_universal in 
    let with_existentials = List.fold_left (fun acc (name, typ) -> mk_exists srk ~name typ acc) eliminated existentials in
    let modified_solver = Solver.make srk (TransitionFormula.make ~exists:(TransitionFormula.exists tf) with_existentials ((j, j') :: (List.filter (fun (s, s') -> typ_symbol srk s != `TyArr && typ_symbol srk s' != `TyArr) (TransitionFormula.symbols tf)))) in 
    let exponentiated = e modified_solver k in 
    substitute_sym srk (fun s ->
      if s = j' then mk_const srk j else
      match List.find_opt (fun (_, z) -> s = z) zs with 
        | Some (a, _) -> mk_select srk (mk_const srk a) (mk_const srk j)
        | None -> mk_const srk s
      ) exponentiated
  in 
  e'
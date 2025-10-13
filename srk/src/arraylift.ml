open Syntax
open Iteration


let reverse_skolem (srk : 'a context) (f : 'a formula) (curr_a : symbol) (i : symbol) : symbol list * 'a formula * ((symbol * symbol * symbol) list)= 
  let array_replacements = ref [] in 
  let get_var (a : symbol) (e : symbol) = 
    match List.find_opt (fun (a', e', _) -> ((compare_symbol a a') = 0) && (compare_symbol e e' = 0)) !array_replacements with
    | None -> (
      let ae = mk_symbol srk `TyInt in 
      array_replacements := ((a, e, ae) :: !array_replacements);
      ae)
    | Some (_, _, ae) -> ae
  in

  let ai = get_var curr_a i in 

  let rec access_array_term (a : 'a arr_term) (e : symbol): 'a arith_term = 
    match ArrTerm.destruct srk a with 
    | `Var (v, _) -> (mk_const srk (get_var (symbol_of_int v) e))
    | `Ite (f, l, r) -> (mk_ite srk f (access_array_term l e) (access_array_term r e))
    | `Store (a, index, value) -> (
        let ae = access_array_term a e in
        mk_ite srk (mk_eq srk index (mk_const srk e)) value ae
    )
    | `App (_, _) -> failwith "Array applications not supported"
  in

  let arith_term_rewriter (a : 'a arith_term) : 'a arith_term = 
    match ArithTerm.destruct srk a with 
    | `Select (arr, index) -> (
      match ArithTerm.destruct srk index with 
      | `Var (v, _) -> access_array_term arr (symbol_of_int v)
      | _ -> failwith "Array index should be a variable"
    )
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
  let existentials = List.filter_map (fun (_, e, ae) -> if (compare_symbol e i = 0) then None else Some ae) !array_replacements in 
  let fc = mk_and srk (List.map (fun (a, e, ae) ->
    if (compare_symbol e i = 0) then mk_true srk 
    else (mk_if srk (mk_eq srk (mk_const srk i) (mk_const srk e)) (mk_eq srk (mk_const srk (get_var a i)) (mk_const srk ae)))
) !array_replacements) in 
  let f'' = mk_exists_const srk ai (mk_and srk [f'; fc]) in 
  existentials, f'', !array_replacements

  

let rec bubble (srk : 'a context) (f : 'a formula) : (symbol list * symbol option * 'a formula * ((symbol * 'a arith_term) list)) = 
  match Formula.destruct srk f with 
  | `Tru | `Fls -> ([], None, f, [])
  | `And ls -> 
    let ls' = List.map (bubble srk) ls in 
    let (exists, forall, parts, array_remappings) = List.fold_left 
    (fun (acc_exists, acc_forall, acc_parts, acc_array_remapping) (exists, forall, part, array_remapping) ->
      let acc_exists = acc_exists @ exists in 
      let acc_array_remapping = acc_array_remapping @ array_remapping in
      match (acc_forall, forall) with 
      | None, None -> (acc_exists, None, part :: acc_parts, acc_array_remapping)
      | Some _, None -> (acc_exists, acc_forall, part :: acc_parts, acc_array_remapping)
      | None, Some _ -> (acc_exists, forall, part :: acc_parts, acc_array_remapping)
      | Some acc_forall', Some forall' -> 
        (acc_exists, Some acc_forall', (substitute_const srk (fun sym -> if (sym = forall') then (mk_const srk acc_forall') else (mk_const srk sym)) part) :: acc_parts, acc_array_remapping))
     ([], None, [], []) (ls') in 
     (exists, forall, mk_and srk parts, array_remappings)
  | `Or ls -> 
    let ls' = List.mapi (fun i e -> i, (bubble srk e)) ls in 
    let b = mk_symbol srk ~name:"b" `TyBool in 
    let (exists, forall, parts, array_remappings) = List.fold_left 
    (fun (acc_exists, acc_forall, acc_parts, acc_array_remapping) (i, (exists, forall, part, array_remapping)) -> 
      let acc_exists = acc_exists @ exists in 
      let acc_array_remapping = acc_array_remapping @ array_remapping in
      match (acc_forall, forall) with 
      | None, None -> (acc_exists, None, part :: acc_parts, acc_array_remapping)
      | Some _, None -> (acc_exists, acc_forall, part :: acc_parts, acc_array_remapping)
      | None, Some _ -> (acc_exists, forall, (mk_and srk [part; mk_eq srk (mk_const srk b) (mk_int srk i)]) :: acc_parts, acc_array_remapping)
      | Some acc_forall', Some forall' -> 
        (acc_exists, Some acc_forall', mk_and srk [substitute_const srk (fun sym -> if sym = forall' then (mk_const srk acc_forall') else (mk_const srk sym)) part; mk_eq srk (mk_const srk b) (mk_int srk i)] :: acc_parts, acc_array_remapping)
    ) ([], None, [], []) ls' in 
    (b :: exists, forall, mk_or srk parts, array_remappings)
  | `Not _ -> failwith "Not is not supported in Skolem fragment"
  | `Quantify (`Forall, name, typ, body) ->
    let (exists, forall, body', array_remapping) = bubble srk body in 
    assert (forall = None); assert (exists = []); assert (typ = `TyInt);
    ([], Some (get_named_symbol srk name), body', array_remapping)
  | `Quantify (`Exists, name, typ, body) ->
    let (exists, forall, body', array_remapping) = bubble srk body in 
    if (typ = `TyArr) 
      then (
        match forall with 
        | None -> failwith "TODO: Should be able to just replace array variable with int"
        | Some i -> 
          let e, f, array_replacements = reverse_skolem srk body' (get_named_symbol srk name) i in 
          let array_remapping' = List.fold_left (fun acc (a, e, ae) -> (ae, mk_select srk (mk_const srk a) (mk_const srk e)) :: acc) array_remapping array_replacements in 
          (e @ exists, None, f, array_remapping')
      ) 
      else ((get_named_symbol srk name) :: exists, forall, body', array_remapping)
  | `Atom _ | `Proposition _ -> ([], None, f, [])
  | `Ite _ -> failwith "Ite should be desugared already"


let get_introduce (srk : 'a context) (array_remappings : (symbol * 'a arith_term) list) : ('a, typ_bool) rewriter = 
  substitute_sym srk (fun s ->
    match List.find_opt (fun (ae, _) -> (compare_symbol s ae) = 0) array_remappings with 
    | None -> mk_const srk s
    | Some (_, e) -> e
  )


let array_exponentiate (srk : 'a context) (e : 'a exp_op) : ('a exp_op) =
  let e' (s : 'a Solver.t) (k : 'a arith_term) : ('a formula) = 
    let tf = Solver.get_transition_formula s in 
    let f = TransitionFormula.formula tf in 
    let existentials, i, skolemized, array_remappings = bubble srk f in 
    let with_universal = match i with
    | None -> skolemized
    | Some i -> mk_forall_const srk i skolemized in 
    let with_existentials = List.fold_left (fun acc s -> mk_exists_const srk s acc) with_universal existentials in
    let modified_solver = Solver.make srk (TransitionFormula.make ~exists:(TransitionFormula.exists tf) with_existentials (TransitionFormula.symbols tf)) in 
    let exponentiated = e modified_solver k in 
    (get_introduce srk array_remappings) exponentiated
  in 
  e'
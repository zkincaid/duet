open Syntax
open Iteration
module SMap = Syntax.Symbol.Map  

(* bubble_sym is an internal helper function for lowering formulas in the skolem array fragment
    to quantified numerical formulas. 
    [bubble_sym srk form] returns a triple of the form (syms, name, form') in which:
        - form ==> \exists syms. \forall name. form'
        - form' contains no array terms
*) 
let bubble_sym (srk : 'a context) (form : 'a formula) : (symbol list * (string option) * 'a formula) = 
  (* rep_map : arr_var -> (index_var -> var) *)
  let (rep_map : (symbol SMap.t) SMap.t ref) = ref SMap.empty in 
  let forall_symbol = mk_symbol srk `TyInt ~name:"forall_index" in

  (* All variables are turned into symbols as we recurse across the formula.
    env maps from variable indices to symbols. 
    qo is the index of the forall variable. 
    Variables with index > qo are existentially quantified outside the forall.
    Note that replace functions only get run after we have found the forall.
  *)
  (* [replace_access arr i env qo] returns a substitute term for arr[i] *)
  let rec replace_access (arr : 'a arr_term) (index : 'a arith_term) (env : (symbol Env.t)) (qo : int) : 'a arith_term = 
    print_string ("Replacing array access: " ^ (ArrTerm.show srk arr) ^ "[" ^ (ArithTerm.show srk index) ^ "]\n");
    match ArrTerm.destruct srk arr with 
    (* Should be i > qo, but is i >= qo to account for special case at line 135 (where we don't have a forall). 
      This is not a problem when we do have a forall, since the assert at line 118 will ensure that we never 
      universally quantify an array variable.
    *)
    | `Var (i, _) -> if i >= qo then ( 
      let array_symbol = Env.find env (i - qo) in 
      let replacement_map = 
        try SMap.find array_symbol !rep_map 
        with Not_found -> failwith "Array variable was never existentially quantified"
      in 
      match ArithTerm.destruct srk index with 
        | `Var (indi, _) -> 
          ((if indi < qo then failwith "Array index variable is bound but should be free");
          let index_symbol = Env.find env (indi - qo) in 
          if (SMap.mem index_symbol replacement_map) then (
            mk_const srk (SMap.find index_symbol replacement_map))
          else (
            let replacement = mk_symbol srk ~name:("rep_" ^ (show_symbol srk array_symbol) ^ "_" ^ (show_symbol srk index_symbol)) `TyInt in
            rep_map := SMap.add array_symbol (SMap.add index_symbol replacement replacement_map) !rep_map;
            mk_const srk replacement
          ))
        | `App (s, []) -> 
          if (SMap.mem s replacement_map) then (
            mk_const srk (SMap.find s replacement_map))
           else (
            let replacement = mk_symbol srk ~name:("rep_" ^ (show_symbol srk array_symbol) ^ "_" ^ (show_symbol srk s)) `TyInt in
            rep_map := SMap.add array_symbol (SMap.add s replacement replacement_map) !rep_map;
            mk_const srk replacement
           )
        | _ -> failwith "Array index should be a variable or a symbol"
      ) 
        else failwith "Array term is not quantified inside the forall"
    | `App (_, _) -> failwith "Array applications not supported"
    | `Ite (f, l, r) -> mk_ite srk (replace f env qo) (replace_access l index env qo) (replace_access r index env qo)
    | `Store (a, store_index, value) ->
      let ae = replace_access a index env qo in 
      mk_ite srk (mk_eq srk store_index index) value ae
  (* replace_at recurses over arith_terms, performing substitution *)
  and replace_at (t : 'a arith_term) (env : (symbol Env.t)) (qo : int) : 'a arith_term = 
    match ArithTerm.destruct srk t with 
    | `Real _ | `App _ -> t
    | `Var (i, _) -> if i > qo then (mk_const srk (Env.find env (i - qo))) else t
    | `Add ls -> mk_add srk (List.map (fun t -> replace_at t env qo) ls)
    | `Mul ls -> mk_mul srk (List.map (fun t -> replace_at t env qo) ls)
    | `Binop (`Div, t1, t2) -> mk_div srk (replace_at t1 env qo) (replace_at t2 env qo)
    | `Binop (`Mod, t1, t2) -> mk_mod srk (replace_at t1 env qo) (replace_at t2 env qo)
    | `Unop (`Neg, t) -> mk_neg srk (replace_at t env qo)
    | `Unop (`Floor, t) -> mk_floor srk (replace_at t env qo)
    | `Ite (f, l, r) -> mk_ite srk (replace f env qo) (replace_at l env qo) (replace_at r env qo)
    | `Select (arr, index) -> replace_access arr index env qo
  (* replace recurses over formulas, performing substitution. *)
  and replace (f : 'a formula) (env : (symbol Env.t)) (qo : int) : ('a formula) = 
    match Formula.destruct srk f with 
    | `Atom (`IsInt t) -> let t' = replace_at t env qo in 
      mk_is_int srk t'
    | `Atom (`Arith (op, t1, t2)) -> 
      (let (t1') = replace_at t1 env qo in 
      let (t2') = replace_at t2 env qo in 
      match op with 
        | `Eq -> (mk_eq srk t1' t2')
        | `Leq -> (mk_leq srk t1' t2')
        | `Lt  -> (mk_lt srk t1' t2'))
    | `Tru | `Fls | `Proposition _ -> f
    | `And ls -> mk_and srk (List.map (fun f -> replace f env qo) ls)
    | `Or ls -> mk_or srk (List.map (fun f -> replace f env qo) ls)
    | `Ite (f, l, r) -> 
      mk_ite srk (replace f env qo) (replace l env qo) (replace r env qo)
    | `Quantify (`Exists, name, typ, body) -> 
        mk_exists srk ~name typ (replace body env (qo + 1))
    | `Quantify (`Forall, _, _, _) -> failwith "Nested foralls not supported in Skolem fragment"
    | `Atom (`ArrEq _) -> failwith "Array equalities should not appear in Skolem fragment"
    | `Not _ -> failwith "Not is not supported in Skolem fragment"
  in

  (* go contains the core "bubbling" logic of this algorithm: 
    we process leading existentials, skolemizing them and adding them to env.
    Once we reach a forall, we stop processing existentials and switch over to replace functions
    to eliminate array terms.
  *)
  let rec go (f : 'a formula) (env : (symbol Env.t)): (symbol list * string option * 'a formula) = 
    let  syms, forall, retf = match Formula.destruct srk f with 
    | `Quantify (`Exists, name, typ, body) -> 
      let new_sym = mk_symbol srk ~name (typ :> typ) in 
      (if typ = `TyArr then (rep_map := (SMap.add new_sym (SMap.empty) !rep_map))); 
      let (syms, forall, body) = go body (Env.push new_sym env) in
      if typ = `TyArr then (
        let introduced_constants = SMap.find new_sym !rep_map |> 
          SMap.bindings |> List.map snd in 
        (introduced_constants @ syms, forall, body)
      ) else (new_sym :: syms, forall, body) 
      
    | `Quantify (`Forall, name, typ, body) -> 
      assert (typ = `TyInt);
      let (body) = replace body (Env.push forall_symbol env) 0  in 
      ([], Some name, body)
    | `And ls -> 
      let (syms, forall, parts) = List.fold_left (fun (syms, forall, parts) f -> 
        let (f_syms, f_forall, f_part) = go f env in 
        f_syms @ syms, (match f_forall with | None -> forall | Some _ -> f_forall), f_part :: parts
        ) ([], None, []) ls in 
      (syms, forall, mk_and srk parts)
    | `Or ls ->
      let branch_var = mk_symbol srk ~name:"branch" `TyInt in 
      let (syms, forall, parts) = List.fold_left (fun (syms, forall, parts) f -> 
          let (f_syms, f_forall, f_part) = go f env in 
          f_syms @ syms, (match f_forall with | None -> forall | Some _ -> f_forall), f_part :: parts
        ) ([], None, []) ls in 
      let parts = List.mapi (fun i part -> mk_and srk [part; mk_eq srk (mk_const srk branch_var) (mk_int srk i)]) parts in 
      (branch_var :: syms, forall, mk_or srk parts)
    | `Atom _ | `Proposition _ -> 
      (* At this point, we want to run replace but cannot because we haven't yet seen a forall.
        Ideally, we could use the equivalence f <=> \forall d. f where f is d-free.
        However, this involves renaming free variables within f to avoid conflict. 

        Instead, we can use a hacky workaround: just running replace as normal. 
        This has a consequence at line 30. 
      *)
      ([], None, replace f env 0)
    | `Tru | `Fls -> ([], None, f)
    | `Ite (f, l, r) -> 
      let f' = mk_or srk [mk_and srk [f ; l]; mk_and srk [mk_not srk f; r]] in 
      go f' env
    | `Not _ -> failwith "Not is not supported in Skolem fragment"
    in 
    print_string "\nBubbled to :\n"; print_string (Formula.show srk (List.fold_left (fun acc sym -> mk_exists_const srk sym acc) (match forall with | None -> retf | Some name -> mk_forall srk ~name `TyInt retf) syms)); print_newline ();
    (syms, forall, retf)
  in
  go form Syntax.Env.empty



(* array_exponentiate lifts exponentiation operator e to work over formulas with arrays. *)
let array_exponentiate (srk : 'a context) (e : 'a exp_op) : ('a TransitionFormula.t -> 'a Syntax.arith_term -> 'a Syntax.formula) = 
  let e' (tf : 'a TransitionFormula.t) (k : 'a arith_term) : ('a formula) = 
    let f = TransitionFormula.formula tf in 
    let array_symbols = List.filter (fun (s, s') -> typ_symbol srk s = `TyArr && typ_symbol srk s' = `TyArr) (TransitionFormula.symbols tf) in 
    let zs = List.fold_left (fun acc (s, s') -> (s, mk_symbol srk `TyInt) :: (s', mk_symbol srk `TyInt) :: acc) [] array_symbols in 
    let j = mk_symbol srk ~name:"j" `TyInt in 
    let j' = mk_symbol srk ~name:"j'" `TyInt in 
    let projected_formula = mk_and srk (f :: (mk_eq srk (mk_const srk j) (mk_const srk j')) :: (List.map (fun (a, z) -> mk_eq srk (mk_select srk (mk_const srk a) (mk_const srk j)) (mk_const srk z)) zs)) in 
    let projected_formula = List.fold_left (fun acc (s, s') -> mk_exists_const srk s' (mk_exists_const srk s acc)) projected_formula (TransitionFormula.symbols tf) in 

    let _, forall, skol = bubble_sym srk projected_formula in
    let with_universal = match forall with 
      | None -> skol
      | Some name -> mk_forall srk ~name `TyInt skol in 
    let eliminated = SrkZ3.qe srk with_universal in 

    let tf'_symbols = (j, j') :: List.map (fun (s, s') -> if (typ_symbol srk s = `TyArr) then (((List.find (fun (sym, _) -> sym = s') zs) |> snd), ((List.find (fun (sym, _) -> sym = s') zs) |> snd)) else (s, s')) (TransitionFormula.symbols tf) in 
    let tf' = TransitionFormula.make ~exists:(fun sym -> (not (List.exists (fun (s, s') -> s = sym || s' = sym) tf'_symbols)) && TransitionFormula.exists tf sym) eliminated tf'_symbols in 
    let solver' = Solver.make srk tf' in

    let exponentiated = e solver' k in 

    let ret = substitute_sym srk (fun s ->
      match List.find_opt (fun (_, z) -> s = z) zs with 
        | Some (a, _) -> mk_select srk (mk_const srk a) (mk_const srk j)
        | None -> mk_const srk s
      ) exponentiated in 
      ret
    in 
    e'


  (* [map_elim ctx f] takes a formula in the array skolem fragment and returns an equisatisfiable formula over numerical variables. *)
  let map_elim (srk : 'a context) (f : 'a formula) : 'a formula = 
    let syms, forall, f = bubble_sym srk f in 
    let f = match forall with 
      | None -> f
      | Some name -> mk_forall srk ~name `TyInt f in 
    let f = List.fold_left (fun acc sym -> mk_exists_const srk sym acc) f syms in 
    f

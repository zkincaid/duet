open Syntax
open Iteration
module SMap = Syntax.Symbol.Map  

let get_or_create_replacement srk replacement_map array_symbol index created_symbols isnt_forall = 
  match Hashtbl.find_opt replacement_map index with 
    | Some replacement -> mk_const srk replacement
    | None -> (
      let replacement = mk_symbol srk `TyInt ~name:("rep_" ^ (show_symbol srk array_symbol) ^ "_" ^ (ArithTerm.show srk index)) in
      Hashtbl.add replacement_map index replacement;
      (if (isnt_forall) then (created_symbols := replacement :: !created_symbols) else ()); (* Update the mutable list *)
      mk_const srk replacement
    )

(* bubble_sym is an internal helper function for lowering formulas in the skolem array fragment
    to quantified numerical formulas. 
    [bubble_sym srk form] returns a triple of the form (syms, is_forall, form') in which:
        - form ==> \exists syms. \forall "". form' if is_forall 
        - form ==> \exists syms. form' if not is_forall
        - form' contains no array terms
*) 
let bubble_sym (srk : 'a context) (form : 'a formula) : (symbol list * (symbol option) * 'a formula) = 
  (* rep_map : arr_var -> (index_var -> var) *)
  let (rep_map : (symbol, ('a arith_term, symbol) Hashtbl.t) Hashtbl.t) = Hashtbl.create 16 in 
  let created_symbols = ref [] in 
  let forall_symbol = mk_symbol srk `TyInt ~name:"forall_index" in

  (* All variables are turned into symbols as we recurse across the formula.
    env maps from variable indices to symbols. 
    qo is the index of the forall variable. 
    Variables with index > qo are existentially quantified outside the forall.
    Note that replace functions only get run after we have found the forall.
  *)
  (* [replace_access arr i env qo] returns a substitute term for arr[i] *)
  let rec replace_access (arr : 'a arr_term) (index : 'a arith_term) (env : (symbol Env.t)) (qo : int) : 'a arith_term = 
    match ArrTerm.destruct srk arr with 
    | `Var (i, _) -> if (i <= qo) then (failwith "Array term is not quantified inside the forall") else ( 
      let array_symbol = Env.find env (i - qo) in 
      let replacement_map = Hashtbl.find rep_map array_symbol in 
      match ArithTerm.destruct srk index with 
        | `Var (indi, _) -> 
          ((if indi < qo then failwith "Array index variable is bound but should be free");
          let index_symbol = Env.find env (indi - qo) in 
          get_or_create_replacement srk replacement_map array_symbol (mk_const srk index_symbol) created_symbols (indi - qo != 0))
        | `App (_, []) | `Real _ -> 
          get_or_create_replacement srk replacement_map array_symbol index created_symbols true
        | _ -> failwith "Array index should be a variable or a symbol"
      ) 
    | `App (_, _) -> failwith "Array applications not supported"
    | `Ite (f, l, r) -> mk_ite srk (replace env qo f) (replace_access l index env qo) (replace_access r index env qo)
    | `Store (a, store_index, value) ->
      let store_index' = replace_at store_index env qo in 
      let index' = replace_at index env qo in 
      let ae = replace_access a index env qo in 
      let ret = mk_ite srk (mk_eq srk store_index' index') value ae in 
      ret
  (* replace_at recurses over arith_terms, performing substitution *)
  and replace_at (t : 'a arith_term) (env : (symbol Env.t)) (qo : int) : 'a arith_term = 
    match ArithTerm.destruct srk t with 
    | `Real _ | `App _ -> t
    | `Var (i, _) -> if i >= qo then (mk_const srk (Env.find env (i - qo))) else t
    | `Add ls -> mk_add srk (List.map (fun t -> replace_at t env qo) ls)
    | `Mul ls -> mk_mul srk (List.map (fun t -> replace_at t env qo) ls)
    | `Binop (`Div, t1, t2) -> mk_div srk (replace_at t1 env qo) (replace_at t2 env qo)
    | `Binop (`Mod, t1, t2) -> mk_mod srk (replace_at t1 env qo) (replace_at t2 env qo)
    | `Unop (`Neg, t) -> mk_neg srk (replace_at t env qo)
    | `Unop (`Floor, t) -> mk_floor srk (replace_at t env qo)
    | `Ite (f, l, r) -> mk_ite srk (replace env qo f) (replace_at l env qo) (replace_at r env qo)
    | `Select (arr, index) -> replace_access arr index env qo
  (* replace recurses over formulas, performing substitution. *)
  and replace (env : (symbol Env.t)) (qo : int) (f : 'a formula) : ('a formula) = 
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
    | `And ls -> mk_and srk (List.map (replace env qo) ls)
    | `Or ls -> mk_or srk (List.map (replace env qo) ls)
    | `Ite (f, l, r) -> 
      mk_ite srk (replace env qo f) (replace env qo l) (replace env qo r)
    | `Quantify (`Exists, name, typ, body) -> 
        mk_exists srk ~name typ (replace env (qo + 1) body)
    | `Quantify (`Forall, _, _, _) -> failwith "Nested foralls not supported in Skolem fragment"
    | `Atom (`ArrEq _) -> failwith "Array equalities should not appear in Skolem fragment"
    | `Not _ -> failwith "Not is not supported in Skolem fragment"
  in

  (* go contains the core "bubbling" logic of this algorithm: 
    we process leading existentials, skolemizing them and adding them to env.
    Once we reach a forall, we stop processing existentials and switch over to replace functions
    to eliminate array terms.
  *)
  (* [go form env] considers the formula \exists env . form
     and returns (syms, is_forall, form') where
        - \exists env . form ==> \exists syms. \forall name. form' if is_forall
        - \exists env . form ==> \exists syms. form' if not is_forall
        - form' contains no array terms *)
  let rec go (f : 'a formula) (env : (symbol Env.t)): (symbol list * bool * 'a formula) = 
     match Formula.destruct srk f with 
    | `Quantify (`Exists, name, typ, body) -> 
      let new_sym = mk_symbol srk ~name (typ :> typ) in 
      (if typ = `TyArr then ((Hashtbl.add rep_map new_sym (Hashtbl.create 16)))); 
      let (syms, forall, body) = go body (Env.push new_sym env) in
      if typ = `TyArr then (
        (syms , forall, body)
      ) else (new_sym :: syms, forall, body) 
      
    | `Quantify (`Forall, _, typ, body) -> 
      assert (typ = `TyInt);
      let (body) = replace (Env.push forall_symbol env) 0 body in 
      let fc = (Hashtbl.fold (fun array_symbol m (acc) -> 
          let ai = get_or_create_replacement srk m array_symbol (mk_const srk forall_symbol) created_symbols false in 
          Hashtbl.fold (fun index replacement acc -> 
            (mk_if srk (mk_eq srk index (mk_const srk forall_symbol)) (mk_eq srk (mk_const srk replacement) ai)) :: acc) m acc
        ) rep_map ([])) in 
      ([], true, mk_and srk (body :: fc))
    | `And ls -> 
      let (syms, forall, parts) = List.fold_left (fun (syms, forall, parts) f -> 
        let (f_syms, f_forall, f_part) = go f env in 
        f_syms @ syms, f_forall || forall, f_part :: parts
        ) ([], false, []) ls in 
      (syms, forall, mk_and srk parts)
    | `Or ls ->
      let branch_var = mk_symbol srk ~name:"branch" `TyInt in 
      let (syms, forall, parts) = List.fold_left (fun (syms, forall, parts) f -> 
          let (f_syms, f_forall, f_part) = go f env in 
          f_syms @ syms, f_forall || forall, f_part :: parts
        ) ([], false, []) ls in 
      let parts = List.mapi (fun i part -> mk_and srk [part; mk_eq srk (mk_const srk branch_var) (mk_int srk i)]) parts in 
      (branch_var :: syms, forall, mk_or srk parts)
    | `Atom _ | `Proposition _ -> 
      (* At this point, we want to run replace but cannot because we haven't yet seen a forall.
        We use the equivalence f <=> \forall d. f where f is d-free
        to map back to the forall case.
      *)
      let f' = substitute srk (fun (i, typ) -> mk_var srk (i + 1) typ) f in 
      go (mk_forall srk `TyInt f') env 
    | `Tru | `Fls -> ([], false, f)
    | `Ite (f, l, r) -> 
      let f' = mk_or srk [mk_and srk [f ; l]; mk_and srk [mk_not srk f; r]] in 
      let f' = rewrite srk ~down:(pos_rewriter srk) f' in 
      go f' env
    | `Not _ -> failwith "Not is not supported in Skolem fragment"
  in
  let syms, forall, retf = go form Syntax.Env.empty in 
  let retf = Hashtbl.fold (fun _ m f -> 
    match Hashtbl.find_opt m (mk_const srk forall_symbol) with 
      | None -> f
      | Some s -> mk_exists_const srk s f
    ) rep_map retf in 
  (!created_symbols @ syms, (if forall then (Some forall_symbol) else None), retf)



(* array_exponentiate lifts exponentiation operator e to work over formulas with arrays. *)
let array_exponentiate (srk : 'a context) (e : 'a exp_op) : ('a TransitionFormula.t -> 'a Syntax.arith_term -> 'a Syntax.formula) = 
  let e' (tf : 'a TransitionFormula.t) (k : 'a arith_term) : ('a formula) = 
    let f = TransitionFormula.formula tf in 
    let array_symbols = List.filter (fun (s, s') -> typ_symbol srk s = `TyArr && typ_symbol srk s' = `TyArr) (TransitionFormula.symbols tf) in 
    let zs = List.fold_left (fun acc (s, s') -> (s, mk_symbol srk `TyInt) :: (s', mk_symbol srk `TyInt) :: acc) [] array_symbols in 
    let j = mk_symbol srk ~name:"j" `TyInt in 
    let j' = mk_symbol srk ~name:"j'" `TyInt in 
    let projected_formula = mk_and srk (f :: (mk_eq srk (mk_const srk j) (mk_const srk j')) :: (List.map (fun (a, z) -> mk_eq srk (mk_select srk (mk_const srk a) (mk_const srk j)) (mk_const srk z)) zs)) in 
    let projected_formula = List.fold_left (fun acc (s, s') ->
      let acc = if typ_symbol srk s = `TyArr then mk_exists_const srk s acc else acc in 
      let acc = if typ_symbol srk s' = `TyArr then mk_exists_const srk s' acc else acc in 
      acc
      ) projected_formula (TransitionFormula.symbols tf) in 

    let existentials, forall, skol = bubble_sym srk projected_formula in
    let with_universal = match forall with 
      | None -> skol
      | Some s -> mk_forall_const srk s skol
    in
      
      
    let with_everything = List.fold_left (fun acc s -> mk_exists_const srk s acc) with_universal existentials in 

    let eliminated = SrkZ3.qe srk with_everything in 

    let tf'_symbols = (j, j') :: List.map (fun (s, s') -> if (typ_symbol srk s = `TyArr) then (((List.find (fun (sym, _) -> sym = s') zs) |> snd), ((List.find (fun (sym, _) -> sym = s') zs) |> snd)) else (s, s')) (TransitionFormula.symbols tf) in 
    let tf' = TransitionFormula.make ~exists:(fun sym -> (not (List.exists (fun (s, s') -> s = sym || s' = sym) tf'_symbols)) && TransitionFormula.exists tf sym) eliminated tf'_symbols in 
    let solver' = Solver.make srk tf' in

    let exponentiated = e solver' k in 

    let ret = substitute_sym srk (fun s ->
      match List.find_opt (fun (_, z) -> s = z) zs with 
        | Some (a, _) -> mk_select srk (mk_const srk a) (mk_const srk j)
        | None -> mk_const srk s
      ) exponentiated in 
    let ret = substitute_sym srk (fun s -> 
        if s = j' then mk_const srk j else mk_const srk s) ret in 
    
    mk_forall_const srk j ret 
    in 
    e'


  (* [map_elim ctx f] takes a formula in the array skolem fragment and returns an equisatisfiable formula over numerical variables. *)
  let map_elim (srk : 'a context) (f : 'a formula) : 'a formula = 
    let syms, forall, f = bubble_sym srk f in 
    let f = match forall with 
      | None -> f 
      | Some s -> mk_forall_const srk s f
    in
    
    let f = List.fold_left (fun acc sym -> mk_exists_const srk sym acc) f syms in 
    f

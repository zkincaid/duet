open Syntax
open Iteration

(* bubble_sym is an internal helper function for lowering formulas in the skolem array fragment
    to quantified numerical formulas. 
    [bubble_sym srk form] returns a triple of the form (syms, is_forall, form') in which:
        - form ==> \exists syms. \forall "". form' if is_forall 
        - form ==> \exists syms. form' if not is_forall
        - form' contains no array terms
*) 
let bubble_sym (srk : 'a context) (form : 'a formula) : (symbol list * (symbol option) * 'a formula) = 
  (* rep_map : arr_var -> (index_term -> var) *)
  let (rep_map : (symbol, ('a, Syntax.typ_arith, symbol) Expr.HT.t) Hashtbl.t) = Hashtbl.create 16 in 
  let leading_existentials = ref [] in 
  let forall_symbol = mk_symbol srk `TyInt ~name:"forall_index" in

  let get_or_create_replacement array_symbol index_term = 
    let replacement_map = Hashtbl.find rep_map array_symbol in 
    match Expr.HT.mem replacement_map index_term with 
      | true -> mk_const srk (Expr.HT.find replacement_map index_term)
      | false -> (
        let name = Format.asprintf "rep_%a_%a"
          (pp_symbol srk) array_symbol
          (ArithTerm.pp srk) index_term
        in
        let replacement = mk_symbol srk `TyInt ~name in
        Expr.HT.add replacement_map index_term replacement;
        leading_existentials := replacement :: !leading_existentials; (* Update the mutable list *)
        mk_const srk replacement
      )
  in

  (* All variables are turned into symbols as we recurse across the formula.
    env maps from variable indices to symbols. 
    qo is the index of the forall variable. 
    Variables with index > qo are existentially quantified outside the forall.
    Note that replace functions only get run after we have found the forall.
  *)
  (* [replace_access arr i env qo] returns a substitute term for arr[i] *)
  let rec replace_access (arr : 'a arr_term) (index : 'a arith_term) (env : (symbol Env.t)) (qo : int) : 'a arith_term = 
    match ArrTerm.destruct srk arr with 
    | `Var (i, _) -> 
        if (i <= qo) then (failwith "Array term is not quantified inside the forall") else ( 
          let array_symbol = Env.find env (i - qo) in 
          match ArithTerm.destruct srk index with 
            | `Var (indi, _) -> 
              ((if indi < qo then failwith "Array index variable is bound but should be free");
              let index_symbol = Env.find env (indi - qo) in 
              get_or_create_replacement array_symbol (mk_const srk index_symbol))
            | `App (_, []) | `Real _ -> 
              get_or_create_replacement array_symbol index
            | _ -> failwith "Array index should be a variable, symbol, or constant"
        ) 
    | `App (_, _) -> failwith "Array applications not supported"
    | `Ite (f, l, r) -> mk_ite srk f (replace_access l index env qo) (replace_access r index env qo)
    | `Store (a, store_index, value) ->
      let ae = replace_access a index env qo in 
      mk_ite srk (mk_eq srk store_index index) value ae 
    in
  let replace env f = 
    fold_rewrite srk 
    ~down:(fun e qo -> match destruct srk e with | `Var (i, t) -> if i >= qo && t != `TyArr then (mk_const srk (Env.find env (i - qo))) else e | _ -> e)
    ~up:(fun e qo -> match destruct srk e with | `Select (arr, index) -> replace_access arr index env qo | _ -> e)
    ~combine:(fun e qo -> match destruct srk e with | `Quantify _ -> qo + 1 | _ -> qo)
    0 f
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
  let rec go (f : 'a formula) (env : (symbol Env.t)): (bool * 'a formula) = 
     match Formula.destruct srk f with 
    | `Quantify (`Exists, name, typ, body) -> 
      let new_sym = mk_symbol srk ~name (typ :> typ) in 
      (if typ = `TyArr then (
        Hashtbl.add rep_map new_sym (Expr.HT.create 16);
        let name = Format.asprintf "rep_%a_univ"
          (pp_symbol srk) new_sym
        in
        Expr.HT.add (Hashtbl.find rep_map new_sym) (mk_const srk forall_symbol) (mk_symbol srk `TyInt ~name);
        let forall, body' = go body (Env.push new_sym env) in 
        let ai = get_or_create_replacement new_sym (mk_const srk forall_symbol) in 
        let fc = BatEnum.fold (fun acc (index, replacement) ->
            (mk_if srk (mk_eq srk index (mk_const srk forall_symbol)) (mk_eq srk (mk_const srk replacement) ai)) :: acc
          ) [] (Expr.HT.enum (Hashtbl.find rep_map new_sym)) in 
        let body'' = mk_exists_const srk (Expr.HT.find (Hashtbl.find rep_map new_sym) (mk_const srk forall_symbol)) 
          (mk_and srk ((body') :: fc))
      in 
        forall, body''
      ) else (
        leading_existentials := new_sym :: !leading_existentials; 
        go body (Env.push new_sym env) 
        ))
    | `Quantify (`Forall, _, typ, body) -> 
      assert (typ = `TyInt);
      let body = replace (Env.push forall_symbol env) body in 
      (true, body)
    | `And ls -> 
      let (forall, parts) = List.fold_left (fun (forall, parts) f -> 
        let (f_forall, f_part) = go f env in 
        f_forall || forall, f_part :: parts
        ) (false, []) ls in 
      (forall, mk_and srk parts)
    | `Or ls ->
      let branch_var = mk_symbol srk ~name:"branch" `TyInt in 
      (leading_existentials := branch_var :: !leading_existentials);
      let (forall, parts) = List.fold_left (fun (forall, parts) f -> 
          let ( f_forall, f_part) = go f env in 
          f_forall || forall, f_part :: parts
        ) (false, []) ls in 
      let parts = List.mapi (fun i part -> mk_and srk [part; mk_eq srk (mk_const srk branch_var) (mk_int srk i)]) parts in 
      (forall, mk_or srk parts)
    | `Atom _ | `Proposition _ -> 
      (* At this point, we want to run replace but cannot because we haven't yet seen a forall.
        We use the equivalence f <=> \forall d. f where f is d-free
        to map back to the forall case.
      *)
      let f' = substitute srk (fun (i, typ) -> mk_var srk (i + 1) typ) f in 
      go (mk_forall srk `TyInt f') env 
    | `Tru | `Fls -> (false, f)
    | `Ite (f, l, r) -> 
      let f' = mk_or srk [mk_and srk [f ; l]; mk_and srk [mk_not srk f; r]] in 
      let f' = rewrite srk ~down:(pos_rewriter srk) f' in 
      go f' env
    | `Not _ -> failwith "Not is not supported in Skolem fragment"
  in
  let forall, retf = go form Syntax.Env.empty in 
  (!leading_existentials, (if forall then (Some forall_symbol) else None), retf)



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


  (* [map_elim ctx f] takes a formula in the array skolem fragment and returns an equivalent formula over numerical variables. *)
  let map_elim (srk : 'a context) (f : 'a formula) : 'a formula = 
    let syms, forall, f = bubble_sym srk f in 
    let f = match forall with 
      | None -> f 
      | Some s -> mk_forall_const srk s f
    in
    
    let f = List.fold_left (fun acc sym -> mk_exists_const srk sym acc) f syms in 
    f

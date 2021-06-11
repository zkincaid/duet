open Syntax
open BatPervasives

include Log.Make(struct let name = "srk.srkZ3" end)

type z3_context = Z3.context
type z3_expr = Z3.Expr.expr
type z3_func_decl = Z3.FuncDecl.func_decl

type 'a open_expr = [
  | `Real of QQ.t
  | `App of z3_func_decl * 'a list
  | `Var of int * typ_fo
  | `Add of 'a list
  | `Mul of 'a list
  | `Binop of [ `Div | `Mod | `Select ] * 'a * 'a
  | `Unop of [ `Floor | `Neg ] * 'a
  | `Store of 'a * 'a * 'a
  | `Tru
  | `Fls
  | `And of 'a list
  | `Or of 'a list
  | `Not of 'a
  | `Ite of 'a * 'a * 'a
  | `Quantify of [`Exists | `Forall] * string * typ_fo * 'a
  | `Atom of [`Eq | `Leq | `Lt] * 'a * 'a
]

let bool_val x =
  match Z3.Boolean.get_bool_value x with
  | Z3enums.L_TRUE -> true
  | Z3enums.L_FALSE -> false
  | Z3enums.L_UNDEF -> invalid_arg "bool_val: not a Boolean"

let rec qq_val ast =
  if Z3.Expr.is_numeral ast then
    QQ.of_string (Z3.Arithmetic.Real.numeral_to_string ast)
  else if Z3.FloatingPoint.is_to_real ast
       || Z3.Arithmetic.is_int2real ast
       || Z3.Arithmetic.is_real2int ast
  then
    qq_val (List.hd (Z3.Expr.get_args ast))
  else invalid_arg "qq_val"

let typ_of_sort sort =
  let open Z3enums in
  match Z3.Sort.get_sort_kind sort with
  | REAL_SORT -> `TyReal
  | INT_SORT -> `TyInt
  | BOOL_SORT -> `TyBool
  | ARRAY_SORT -> `TyArr
  | _ -> invalid_arg "typ_of_sort"

let rec sort_of_typ z3 = function
  | `TyInt -> Z3.Arithmetic.Integer.mk_sort z3
  | `TyReal -> Z3.Arithmetic.Real.mk_sort z3
  | `TyBool -> Z3.Boolean.mk_sort z3
  | `TyArr -> 
    Z3.Z3Array.mk_sort z3 (sort_of_typ z3 `TyInt) (sort_of_typ z3 `TyInt)

let rec eval alg ast =
  let open Z3 in
  let open Z3enums in
  match AST.get_ast_kind (Expr.ast_of_expr ast) with
  | APP_AST -> begin
      let decl = Expr.get_func_decl ast in
      let args = List.map (eval alg) (Expr.get_args ast) in
      match FuncDecl.get_decl_kind decl, args with
      | (OP_UNINTERPRETED, args) -> alg (`App (decl, args))
      | (OP_ADD, args) -> alg (`Add args)
      | (OP_MUL, args) -> alg (`Mul args)
      | (OP_SUB, [x;y]) -> alg (`Add [x; alg (`Unop (`Neg, y))])
      | (OP_UMINUS, [x]) -> alg (`Unop (`Neg, x))
      | (OP_MOD, [x;y]) -> alg (`Binop (`Mod, x, y))
      | (OP_IDIV, [x;y]) -> alg (`Unop (`Floor, alg (`Binop (`Div, x, y))))
      | (OP_DIV, [x;y]) -> alg (`Binop (`Div, x, y))
      | (OP_TO_REAL, [x]) -> x
      | (OP_TO_INT, [x]) -> alg (`Unop (`Floor, x))

      | (OP_STORE, [a; i; v]) -> alg (`Store (a, i, v))
      | (OP_SELECT, [a; i]) -> alg (`Binop(`Select, a, i))
      
      | (OP_TRUE, []) -> alg `Tru
      | (OP_FALSE, []) -> alg `Fls
      | (OP_AND, args) -> alg (`And args)
      | (OP_OR, args) -> alg (`Or args)
      | (OP_IMPLIES, [phi;psi]) -> alg (`Or [alg (`Not phi); psi])
      | (OP_IFF, [phi;psi]) ->
        alg (`Or [alg (`And [phi; psi]);
                  alg (`Not (alg (`Or [phi; psi])))])
      | (OP_NOT, [phi]) -> alg (`Not phi)
      | (OP_EQ, [s; t]) -> alg (`Atom (`Eq, s, t))
      | (OP_LE, [s; t]) -> alg (`Atom (`Leq, s, t))
      | (OP_GE, [s; t]) -> alg (`Atom (`Leq, t, s))
      | (OP_LT, [s; t]) -> alg (`Atom (`Lt, s, t))
      | (OP_GT, [s; t]) -> alg (`Atom (`Lt, t, s))
      | (OP_ITE, [cond; s; t]) -> alg (`Ite (cond, s, t))
      | (_, _) -> invalid_arg ("eval: unknown application: "
                               ^ (Expr.to_string ast))
    end
  | NUMERAL_AST ->
    alg (`Real (qq_val ast))
  | VAR_AST ->
    let index = Z3.Quantifier.get_index ast in
    alg (`Var (index, (typ_of_sort (Expr.get_sort ast))))
  | QUANTIFIER_AST ->
    let ast = Z3.Quantifier.quantifier_of_expr ast in
    let qt =
      if Z3.Quantifier.is_existential ast then `Exists
      else `Forall
    in
    List.fold_right2
      (fun name sort body ->
         alg (`Quantify (qt,
                         Z3.Symbol.to_string name,
                         typ_of_sort sort,
                         body)))
      (Z3.Quantifier.get_bound_variable_names ast)
      (Z3.Quantifier.get_bound_variable_sorts ast)
      (eval alg (Z3.Quantifier.get_body ast))
  | FUNC_DECL_AST
  | SORT_AST
  | UNKNOWN_AST -> invalid_arg "eval: unknown ast type"

let _mk_quantifier_simplify_tactic z3 =
  let open Z3 in
  let open Tactic in
  let mk_tactic = mk_tactic z3 in
  let sym = Symbol.mk_string z3 in
  let pull_ite =
    let p = Params.mk_params z3 in
    Params.add_bool p (sym "pull-cheap-ite") true;
    Params.add_bool p (sym "local-ctx") true;
    Params.add_int p (sym "local-ctx-limit") 10000000;
    p
  in
  let ctx_simp =
    let p = Params.mk_params z3 in
    Params.add_int p (sym "max-depth") 30;
    Params.add_int p (sym "max-steps") 5000000;
    p
  in
  let solve_eqs =
    when_ z3
      (Probe.not_ z3 (Probe.mk_probe z3 "has-patterns"))
      (mk_tactic "solve-eqs")
  in
  let f t t' = Tactic.and_then z3 t t' [] in
  List.fold_left f (mk_tactic "simplify") [
    mk_tactic "propagate-values";
    using_params z3 (mk_tactic "ctx-simplify") ctx_simp;
    using_params z3 (mk_tactic "simplify") pull_ite;
    solve_eqs;
    mk_tactic "elim-uncnstr";
    mk_tactic "simplify"]

let mk_quantified ctx qt ?name:(name="_") typ phi =
  let mk = match qt with
    | `Exists -> Z3.Quantifier.mk_exists
    | `Forall -> Z3.Quantifier.mk_forall
  in
  mk
    ctx
    [sort_of_typ ctx typ]
    [Z3.Symbol.mk_string ctx name]
    phi
    None
    []
    []
    None
    None
  |> Z3.Quantifier.expr_of_quantifier

let z3_of_symbol z3 sym = Z3.Symbol.mk_int z3 (int_of_symbol sym)

let decl_of_symbol z3 srk sym =
  let (param_sorts, return_sort) = match typ_symbol srk sym with
    | `TyInt | `TyReal | `TyBool | `TyArr ->
      invalid_arg "decl_of_symbol: not a function symbol"
    | `TyFun (params, return) ->
      (List.map (sort_of_typ z3) params, sort_of_typ z3 return)
  in
  let z3sym = z3_of_symbol z3 sym in
  Z3.FuncDecl.mk_func_decl z3 z3sym param_sorts return_sort

let rec z3_of_expr srk z3 expr =
  match Expr.refine_coarse srk expr with
  | `Term t -> z3_of_term srk z3 t
  | `Formula phi -> z3_of_formula srk z3 phi

and z3_of_term srk z3 term =
  match Term.refine srk term with
  | `ArithTerm t -> z3_of_arith_term srk z3 t
  | `ArrTerm t -> z3_of_arr_term srk z3 t

and z3_of_arr_term (srk : 'a context) z3 (term : 'a arr_term) =
  let alg = function
    | `App (sym, []) ->
      let sort = match typ_symbol srk sym with
        | `TyArr -> sort_of_typ z3 `TyArr
        | `TyInt | `TyReal | `TyBool | `TyFun (_,_) ->
          invalid_arg "z3_of_arr_term: ill-typed application"
      in
      let decl = Z3.FuncDecl.mk_const_decl z3 (z3_of_symbol z3 sym) sort in
      Z3.Expr.mk_const_f z3 decl

    | `App (func, args) ->
      let decl = decl_of_symbol z3 srk func in
      Z3.Expr.mk_app z3 decl (List.map (z3_of_expr srk z3) args)

    | `Var (i, `TyArr) ->
      Z3.Quantifier.mk_bound z3 i (sort_of_typ z3 `TyArr)
    | `Store (a, i, v) -> 
      Z3.Z3Array.mk_store z3 a (z3_of_arith_term srk z3 i) (z3_of_arith_term srk z3 v)
    | `Ite (cond, bthen, belse) ->
      Z3.Boolean.mk_ite z3 (z3_of_formula srk z3 cond) bthen belse
  in
  ArrTerm.eval srk alg term

and z3_of_arith_term (srk : 'a context) z3 (term : 'a arith_term) =
  let alg = function
    | `Real qq ->
      begin match QQ.to_zz qq with
        | Some zz -> Z3.Arithmetic.Integer.mk_numeral_s z3 (ZZ.show zz)
        | None -> Z3.Arithmetic.Real.mk_numeral_s z3 (QQ.show qq)
      end
    | `App (sym, []) ->
      let sort = match typ_symbol srk sym with
        | `TyInt -> sort_of_typ z3 `TyInt
        | `TyReal -> sort_of_typ z3 `TyReal
        | `TyBool | `TyFun (_,_) | `TyArr ->
          invalid_arg "z3_of.term: ill-typed application"
      in
      let decl = Z3.FuncDecl.mk_const_decl z3 (z3_of_symbol z3 sym) sort in
      Z3.Expr.mk_const_f z3 decl

    | `App (func, args) ->
      let decl = decl_of_symbol z3 srk func in
      Z3.Expr.mk_app z3 decl (List.map (z3_of_expr srk z3) args)

    | `Var (i, `TyInt) ->
      Z3.Quantifier.mk_bound z3 i (sort_of_typ z3 `TyInt)
    | `Var (i, `TyReal) ->
      Z3.Quantifier.mk_bound z3 i (sort_of_typ z3 `TyReal)
    | `Add sum -> Z3.Arithmetic.mk_add z3 sum
    | `Mul product -> Z3.Arithmetic.mk_mul z3 product
    | `Binop (`Div, s, t) -> Z3.Arithmetic.mk_div z3 s t
    | `Binop (`Mod, s, t) -> Z3.Arithmetic.Integer.mk_mod z3 s t
    | `Unop (`Floor, t) -> Z3. Arithmetic.Real.mk_real2int z3 t
    | `Unop (`Neg, t) -> Z3.Arithmetic.mk_unary_minus z3 t
    | `Select (a, i) -> Z3.Z3Array.mk_select z3 (z3_of_arr_term srk z3 a) i
    | `Ite (cond, bthen, belse) ->
      Z3.Boolean.mk_ite z3 (z3_of_formula srk z3 cond) bthen belse
  in
  ArithTerm.eval srk alg term

and z3_of_formula srk z3 =
  let of_arith_term = z3_of_arith_term srk z3 in
  let of_arr_term = z3_of_arr_term srk z3 in
  let alg = function
    | `Tru -> Z3.Boolean.mk_true z3
    | `Fls -> Z3.Boolean.mk_false z3
    | `And conjuncts -> Z3.Boolean.mk_and z3 conjuncts
    | `Or [phi; psi] ->
      begin match Z3.AST.get_ast_kind (Z3.Expr.ast_of_expr phi) with
        | Z3enums.APP_AST -> begin
            let decl = Z3.Expr.get_func_decl phi in
            match Z3.FuncDecl.get_decl_kind decl, Z3.Expr.get_args phi with
            | (Z3enums.OP_NOT, [phi]) -> Z3.Boolean.mk_implies z3 phi psi
            | (_, _) -> Z3.Boolean.mk_or z3 [phi; psi]
          end
        | _ -> Z3.Boolean.mk_or z3 [phi; psi]
      end
    | `Or disjuncts -> Z3.Boolean.mk_or z3 disjuncts
    | `Not phi -> Z3.Boolean.mk_not z3 phi
    | `Quantify (qt, name, typ, phi) ->
      mk_quantified z3 qt ~name typ phi
    | `Atom (`Arith (`Eq, s, t)) -> Z3.Boolean.mk_eq z3 (of_arith_term s) (of_arith_term t)
    | `Atom (`Arith (`Leq, s, t)) -> Z3.Arithmetic.mk_le z3 (of_arith_term s) (of_arith_term t)
    | `Atom (`Arith (`Lt, s, t)) -> Z3.Arithmetic.mk_lt z3 (of_arith_term s) (of_arith_term t)
    | `Atom (`ArrEq (s, t)) -> Z3.Boolean.mk_eq z3 (of_arr_term s) (of_arr_term t)
    | `Proposition (`Var i) ->
      Z3.Quantifier.mk_bound z3 i (sort_of_typ z3 `TyBool)
    | `Proposition (`App (p, [])) ->
      let decl =
        Z3.FuncDecl.mk_const_decl z3
          (z3_of_symbol z3 p)
          (sort_of_typ z3 `TyBool)
      in
      Z3.Expr.mk_const_f z3 decl
    | `Proposition (`App (predicate, args)) ->
      let decl = decl_of_symbol z3 srk predicate in
      Z3.Expr.mk_app z3 decl (List.map (z3_of_expr srk z3) args)
    | `Ite (cond, bthen, belse) -> Z3.Boolean.mk_ite z3 cond bthen belse
  in
  Formula.eval_memo srk alg

type 'a gexpr = ('a, typ_fo) Syntax.expr
let of_z3 context sym_of_decl expr =
  let arith_term = Syntax.Expr.arith_term_of context in
  let arr_term = Syntax.Expr.arr_term_of context in
  let formula = Syntax.Expr.formula_of context in
  let alg : (('a, typ_fo) Syntax.expr) open_expr -> ('a, typ_fo) Syntax.expr =
    function
    | `Real qq -> (mk_real context qq :> 'a gexpr)
    | `Var (i, typ) -> mk_var context i typ
    | `App (decl, args) ->
      let const_sym = sym_of_decl decl in
      mk_app context const_sym args
    | `Add sum -> (mk_add context (List.map arith_term sum) :> 'a gexpr)
    | `Mul product -> (mk_mul context (List.map arith_term product) :> 'a gexpr)
    | `Binop (`Div, s, t) -> (mk_div context (arith_term s) (arith_term t) :> 'a gexpr)
    | `Binop (`Mod, s, t) -> (mk_mod context (arith_term s) (arith_term t) :> 'a gexpr) 
    | `Binop (`Select, a, i) -> (mk_select context (arr_term a) (arith_term i) :> 'a gexpr) 
    | `Unop (`Floor, t) -> (mk_floor context (arith_term t) :> 'a gexpr)
    | `Unop (`Neg, t) -> (mk_neg context (arith_term t) :> 'a gexpr)
    | `Store (a, i, v) -> (mk_store context (arr_term a) (arith_term i) (arith_term v) :> 'a gexpr)
    | `Tru -> (mk_true context :> 'a gexpr)
    | `Fls -> (mk_false context :> 'a gexpr)
    | `And conjuncts ->
      (mk_and context (List.map formula conjuncts) :> 'a gexpr)
    | `Or disjuncts -> (mk_or context (List.map formula disjuncts) :> 'a gexpr)
    | `Not phi -> (mk_not context (formula phi) :> 'a gexpr)
    | `Quantify (`Exists, name, typ, phi) ->
      (mk_exists context ~name:name typ (formula phi) :> 'a gexpr)
    | `Quantify (`Forall, name, typ, phi) ->
      (mk_forall context ~name:name typ (formula phi) :> 'a gexpr)
    | `Atom (`Eq, s, t) ->
      begin match Expr.refine context s, Expr.refine context t with
        | `ArithTerm s, `ArithTerm t -> (mk_eq context s t :> 'a gexpr)
        | `ArrTerm a, `ArrTerm b -> (mk_arr_eq context a b :> 'a gexpr)
        | `Formula phi, `Formula psi ->
          (mk_or context [mk_and context [phi; psi];
                          mk_and context [mk_not context phi;
                                          mk_not context psi]]
           :> 'a gexpr)
        | _, _ -> invalid_arg "of_z3: equal"
      end
    | `Atom (`Leq, s, t) -> (mk_leq context (arith_term s) (arith_term t) :> 'a gexpr)
    | `Atom (`Lt, s, t) -> (mk_lt context (arith_term s) (arith_term t) :> 'a gexpr)
    | `Ite (cond, bthen, belse) -> mk_ite context (formula cond) bthen belse
  in
  eval alg expr

(* sym_of_decl is sufficient for round-tripping, since srk symbols become
   Z3 int symbols *)
let sym_of_decl decl =
  let sym = Z3.FuncDecl.get_name decl in
  match Z3.Symbol.kind sym with
  | STRING_SYMBOL -> assert false
   (* let name = Z3.Symbol.get_string sym in
    if is_registered_name srk name
    then get_named_symbol srk name
    else register_named_symbol srk name; *)
  | INT_SYMBOL -> symbol_of_int (Z3.Symbol.get_int sym)

let term_of_z3 context ?sym_of_decl:(sym_of_decl = sym_of_decl) term =
  match Expr.refine_coarse context (of_z3 context sym_of_decl term) with
  | `Term t -> t
  | _ -> invalid_arg "term_of"

let formula_of_z3 context ?sym_of_decl:(sym_of_decl = sym_of_decl) phi =
  match Expr.refine context (of_z3 context sym_of_decl phi) with
  | `Formula phi -> phi
  |  _ -> invalid_arg "formula_of"

let expr_of_z3 context ?sym_of_decl:(sym_of_decl = sym_of_decl) expr = 
  of_z3 context sym_of_decl expr

type 'a solver =
  { srk : 'a context;
    z3 : z3_context;
    s : Z3.Solver.solver;
    formula_of : z3_expr -> 'a formula;
    of_formula : 'a formula -> z3_expr }

let mk_solver ?(context=Z3.mk_context []) ?(theory="") srk =
  let s = 
    if theory = "" then
      Z3.Solver.mk_simple_solver context
    else
      Z3.Solver.mk_solver_s context theory
  in
  let of_formula = z3_of_formula srk context in
  let formula_of t = formula_of_z3 srk t in
  { srk; z3 = context; s; of_formula; formula_of }

module Solver = struct
  type 'a t = 'a solver
  let add solver formulas =
    Z3.Solver.add solver.s (List.map solver.of_formula formulas)

  let push solver = Z3.Solver.push solver.s
  let pop solver = Z3.Solver.pop solver.s
  let reset solver = Z3.Solver.reset solver.s

  let check solver args =
    let args = List.map solver.of_formula args in
    try
      match Log.time "solver.check" (Z3.Solver.check solver.s) args with
      | Z3.Solver.SATISFIABLE -> `Sat
      | Z3.Solver.UNSATISFIABLE -> `Unsat
      | Z3.Solver.UNKNOWN -> `Unknown
    with Z3.Error x ->
      logf ~level:`warn "Caught Z3 exception: %s" x;
      `Unknown


  let expr_of_sym srk z3 symbol =
    let sort =
      match typ_symbol srk symbol with
      | `TyReal -> sort_of_typ z3 `TyReal
      | `TyInt -> sort_of_typ z3 `TyInt
      | `TyBool -> sort_of_typ z3 `TyBool
      | _ -> assert false
    in
    let decl =
      Z3.FuncDecl.mk_const_decl z3 (z3_of_symbol z3 symbol) sort
    in
    Z3.Expr.mk_const_f z3 decl

  let model_get_value srk z3 m sym =
    match typ_symbol srk sym with
    | `TyReal | `TyInt ->
      let t = expr_of_sym srk z3 sym in
      begin match Z3.Model.eval m t true with
        | Some x -> `Real (qq_val x)
        | None -> assert false
      end
    | `TyBool ->
      let t = expr_of_sym srk z3 sym in
      begin match Z3.Model.eval m t true with
        | Some x -> `Bool (bool_val x)
        | None -> assert false
      end
    | `TyArr -> assert false (* TODO: intepretations for arrays *)
    | `TyFun (params, _) ->
      let decl = decl_of_symbol z3 srk sym in
      let finterp = match Z3.Model.get_func_interp m decl with
        | None -> assert false
        | Some interp -> interp
      in
      let formals =
        List.mapi (fun i typ -> mk_var srk i typ) params
      in
      let default =
        of_z3 srk sym_of_decl
          (Z3.Model.FuncInterp.get_else finterp)
      in
      let mk_eq x y = (* type-generic equality *)
        match Expr.refine srk x, Expr.refine srk y with
        | `ArithTerm x, `ArithTerm y ->
          (mk_eq srk x y :> ('a, 'typ_fo) Syntax.expr)
        | `Formula x, `Formula y ->
          (mk_iff srk x y :> ('a, 'typ_fo) Syntax.expr)
        | _, _ -> assert false
      in
      let func =
        List.fold_right (fun entry rest ->
            let value =
              Z3.Model.FuncInterp.FuncEntry.get_value entry
              |> of_z3 srk sym_of_decl
            in
            let cond =
              List.map2 (fun formal value ->
                  mk_eq formal (of_z3 srk sym_of_decl value))
                formals
                (Z3.Model.FuncInterp.FuncEntry.get_args entry)
              |> mk_and srk
            in
            mk_ite srk cond value rest)
          (Z3.Model.FuncInterp.get_entries finterp)
          default
      in
      `Fun func

  let get_model ?(symbols=[]) solver =
    let srk = solver.srk in
    let z3 = solver.z3 in
    match check solver [] with
    | `Sat ->
      begin match Z3.Solver.get_model solver.s with
        | Some m ->
          `Sat (Interpretation.wrap ~symbols srk (model_get_value srk z3 m))
        | None -> `Unknown
      end
    | `Unsat -> `Unsat
    | `Unknown -> `Unknown

  let get_concrete_model solver symbols =
    let srk = solver.srk in
    let z3 = solver.z3 in
    match check solver [] with
    | `Sat ->
      begin match Z3.Solver.get_model solver.s with
        | Some m ->
          `Sat (Interpretation.wrap ~symbols srk (model_get_value srk z3 m))
        | None -> `Unknown
      end
    | `Unsat -> `Unsat
    | `Unknown -> `Unknown

  let to_string solver = Z3.Solver.to_string solver.s

  let get_unsat_core solver assumptions =
    match check solver assumptions with
    | `Sat -> `Sat
    | `Unknown -> `Unknown
    | `Unsat ->
      `Unsat (List.map solver.formula_of (Z3.Solver.get_unsat_core solver.s))

  let get_reason_unknown solver = Z3.Solver.get_reason_unknown solver.s
end

let optimize_box ?(context=Z3.mk_context []) srk phi objectives =
  let open Z3.Optimize in
  let z3 = context in
  let opt = mk_opt z3 in
  let params = Z3.Params.mk_params z3 in
  let sym = Z3.Symbol.mk_string z3 in
  Z3.Params.add_symbol params (sym ":opt.priority") (sym "box");
  set_parameters opt params;
  add opt [z3_of_formula srk z3 phi];
  let mk_handles t =
    let z3t = z3_of_arith_term srk z3 t in
    (minimize opt z3t, maximize opt z3t)
  in
  let handles = List.map mk_handles objectives in
  let mk_interval (lo, hi) =
    let lower =
      let lo = get_lower lo in
      if Z3.Expr.is_numeral lo then
        Some (qq_val lo)
      else if Z3.Expr.to_string lo = "(* (- 1) oo)" then
        None
      else if Z3.Expr.to_string lo = "epsilon" then
        Some QQ.zero
      else if Z3.Arithmetic.is_mul lo then
        (* x * epsilon *)
        Some QQ.zero
      else if Z3.Arithmetic.is_add lo then
        (* x + y*epsilon *)
        Some (qq_val (List.hd (Z3.Expr.get_args lo)))
      else
        Log.fatalf "Smt.optimize_box: %s" (Z3.Expr.to_string lo)
    in
    let upper =
      let hi = get_lower hi in
      if Z3.Expr.is_numeral hi then
        Some (qq_val hi)
      else if Z3.Expr.to_string hi = "oo" then
        None
      else if Z3.Arithmetic.is_mul hi then
        (* x*epsilon *)
        Some QQ.zero
      else if Z3.Arithmetic.is_add hi then
        (* x - y*epsilon *)
        Some (qq_val (List.hd (Z3.Expr.get_args hi)))
      else
        Log.fatalf "Smt.optimize_box: %s" (Z3.Expr.to_string hi)
    in
    Interval.make lower upper
  in
  try
    match check opt with
    | Z3.Solver.SATISFIABLE -> `Sat (List.map mk_interval handles)
    | Z3.Solver.UNSATISFIABLE -> `Unsat
    | Z3.Solver.UNKNOWN -> `Unknown
  with Z3.Error x ->
    logf ~level:`warn "Caught Z3 exception: %s" x;
    `Unknown

let interpolate_seq ?context:_ _ _ =
  failwith "SrkZ3.interpolate_seq not implemented"

let load_smtlib2 ?(context=Z3.mk_context []) srk str =
  let z3 = context in
  let ast = Z3.SMT.parse_smtlib2_string z3 str [] [] [] [] in
  let sym_of_decl =
    let cos =
      Memo.memo (fun (name, typ) ->
          mk_symbol srk ~name typ)
    in
    fun decl ->
      let open Z3 in
      let sym = FuncDecl.get_name decl in
      match FuncDecl.get_domain decl with
      | [] ->
        cos (Symbol.to_string sym, typ_of_sort (FuncDecl.get_range decl))
      | dom ->
        let typ =
          `TyFun (List.map typ_of_sort dom,
                  typ_of_sort (FuncDecl.get_range decl))
        in
        cos (Symbol.to_string sym, typ)
  in
  Z3.AST.ASTVector.to_expr_list ast
  |> List.map (fun expr ->
         match Expr.refine_coarse srk (of_z3 srk sym_of_decl expr) with
         | `Formula phi -> phi
         | `Term _ -> invalid_arg "load_smtlib2")
  |> mk_and srk

let of_goal srk g =
  List.map (formula_of_z3 srk) (Z3.Goal.get_formulas g)
  |> mk_and srk

let of_apply_result srk result =
  List.map (of_goal srk) (Z3.Tactic.ApplyResult.get_subgoals result)
  |> mk_and srk

let qe ?(context=Z3.mk_context []) srk phi =
  let open Z3 in
  let z3 = context in
  let solve = Tactic.mk_tactic z3 "qe" in
  let simpl = Tactic.mk_tactic z3 "simplify" in
  let qe = Tactic.and_then z3 solve simpl [] in
  let g = Goal.mk_goal z3 false false false in
  Goal.add g [z3_of_formula srk z3 phi];
  of_apply_result srk (Tactic.apply qe g None)

let simplify ?(context=Z3.mk_context []) srk phi =
  let open Z3 in
  let open Tactic in
  let z3 = context in
  let mk_tactic = mk_tactic z3 in
  let solve_eqs =
    when_ z3
      (Probe.not_ z3 (Probe.mk_probe z3 "has-patterns"))
      (mk_tactic "solve-eqs")
  in
  let simplify =
    List.fold_left
      (fun t t' -> Tactic.and_then z3 t t' [])
      (mk_tactic "simplify")
      [mk_tactic "propagate-values";
       mk_tactic "simplify";
       solve_eqs;
       mk_tactic "simplify"]
  in
  let g = Goal.mk_goal z3 false false false in
  Goal.add g [z3_of_formula srk z3 phi];
  try
    of_apply_result srk (Tactic.apply simplify g None)
  with _ -> assert false

module CHC = struct
  type 'a solver =
    { z3 : Z3.context;
      srk : 'a context;
      error : symbol;
      mutable head_relations : Symbol.Set.t;
      fp : Z3.Fixedpoint.fixedpoint }

  let mk_solver ?(context=Z3.mk_context []) srk =
    let fp = Z3.Fixedpoint.mk_fixedpoint context in
    let error = mk_symbol srk ~name:"error" (`TyFun ([], `TyBool)) in
    let error_decl = decl_of_symbol context srk error in
    let params = Z3.Params.mk_params context in
    let sym x = Z3.Symbol.mk_string context x in
    Z3.Params.add_bool params (sym "xform.slice") false;
    Z3.Params.add_bool params (sym "xform.inline_linear") false;
    Z3.Params.add_bool params (sym "xform.inline_eager") false;
    Z3.Fixedpoint.set_parameters fp params;

    Z3.Fixedpoint.register_relation fp error_decl;
    { z3 = context; srk; error; fp; head_relations = Symbol.Set.empty }

  let register_relation solver relation =
    let srk = solver.srk in
    let decl = decl_of_symbol solver.z3 srk relation in
    Z3.Fixedpoint.register_relation solver.fp decl

  let add solver phis =
    Z3.Fixedpoint.add solver.fp
      (List.map (z3_of_formula solver.srk solver.z3) phis)

  module M = SrkUtil.Int.Map

  let add_rule solver hypothesis conclusion =
    let srk = solver.srk in
    let z3 = solver.z3 in
    (* The hypothesis is assumed to not simplify to true/false -- otherwise,
       var_table isn't initialized *)
    let var_table = free_vars (mk_if srk hypothesis conclusion) in
    let rename =
      let table = Hashtbl.create 991 in
      BatHashtbl.enum var_table
      |> BatEnum.iteri (fun i (j, typ) -> Hashtbl.add table j (mk_var srk i typ));
      fun (i, _) -> Hashtbl.find table i
    in
    let rule =
      match destruct srk conclusion with
      | `App (r, _) ->
        let hypothesis =
          z3_of_formula srk z3 (substitute srk rename hypothesis)
        in
        let conclusion =
          z3_of_formula srk z3 (substitute srk rename conclusion)
        in
        solver.head_relations <- Symbol.Set.add r solver.head_relations;
        Z3.Boolean.mk_implies z3 hypothesis conclusion
      | _ ->
        let hypothesis =
          mk_and srk [hypothesis; (mk_not srk conclusion)]
          |> substitute srk rename
          |> z3_of_formula srk z3
        in
        let conclusion =
          mk_app srk solver.error []
          |> z3_of_formula srk z3
        in
        Z3.Boolean.mk_implies z3 hypothesis conclusion
    in
    let quantified_rule =
      let types =
        BatHashtbl.values var_table
        /@ (sort_of_typ z3)
        |> BatList.of_enum
      in
      let names =
        List.map (fun _ -> Z3.Symbol.mk_string z3 "_") types
      in
      Z3.Quantifier.mk_forall z3 types names rule None [] [] None None
      |> Z3.Quantifier.expr_of_quantifier
    in
    Z3.Fixedpoint.add_rule solver.fp quantified_rule None

  let add_rule solver hypothesis conclusion =
    let srk = solver.srk in
    let z3 = solver.z3 in
    match destruct srk (mk_if srk hypothesis conclusion) with
    | `Tru -> ()
    | `Fls ->
      let err_rule =
        Z3.Boolean.mk_implies
          z3
          (z3_of_formula srk z3 (mk_true srk))
          (z3_of_formula srk z3 (mk_app srk solver.error []))
      in
      Z3.Fixedpoint.add_rule solver.fp err_rule None
    | _ -> add_rule solver hypothesis conclusion

  let check solver =
    let goal =
      z3_of_formula solver.srk solver.z3 (mk_app solver.srk solver.error [])
    in
    try
      match Z3.Fixedpoint.query solver.fp goal with
      | Z3.Solver.UNSATISFIABLE -> `Sat
      | Z3.Solver.SATISFIABLE -> `Unsat
      | Z3.Solver.UNKNOWN -> `Unknown
    with Z3.Error x ->
      logf ~level:`warn "Caught Z3 exception: %s" x;
      `Unknown

  let get_solution solver relation =
    let srk = solver.srk in
    let z3 = solver.z3 in
    let decl = decl_of_symbol z3 srk relation in
    if Symbol.Set.mem relation solver.head_relations then
      match Z3.Fixedpoint.get_cover_delta solver.fp (-1) decl with
      | Some inv -> formula_of_z3 srk inv
      | None -> assert false
    else
      mk_false srk

  let to_string solver = Z3.Fixedpoint.to_string solver.fp
end

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
  | `IsInt of 'a list
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
      | (OP_UNINTERPRETED, args) ->
         alg (`App (decl, args))
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
      | (OP_SELECT, [a; i]) -> alg (`Binop (`Select, a, i))

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
      | (OP_IS_INT, [s]) -> alg (`IsInt [s])
      | (OP_DISTINCT, xs) ->
         let neq x y = alg (`Not (alg (`Atom (`Eq, x, y)))) in
         let rec all_pairs = function
           | [] -> [alg `Tru]
           | y1 :: ys ->
              List.fold_left (fun pairs y2 -> neq y1 y2 :: pairs) (all_pairs ys) ys
         in
         alg (`And (all_pairs xs))
      | (OP_XOR, xs) ->
        let xor x y =
          alg (`Or [alg (`And [alg (`Not x); y]);
                    alg (`And [x; alg (`Not y)])])
        in
        BatList.reduce xor xs

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

(* retrieve the Z3 declaration of a srk symbol *)
let decl_of_symbol z3 srk sym =
  let (param_sorts, return_sort) = match typ_symbol srk sym with
    | `TyInt | `TyReal | `TyBool | `TyArr ->
      invalid_arg "decl_of_symbol: not a function symbol"
    | `TyFun (params, return) -> (* function symbols are, e.g. spacer relations *)
      (List.map (sort_of_typ z3) params, sort_of_typ z3 return)
  in
  let z3sym = z3_of_symbol z3 sym in
  Z3.FuncDecl.mk_func_decl z3 z3sym param_sorts return_sort

(* Z3 constant corresponding to a non-function srk symbol.  The Z3-side name
   is an int symbol carrying the srk symbol id (see z3_of_symbol) *)
let z3_const_of_symbol srk z3 sym =
  match typ_symbol srk sym with
  | `TyInt | `TyReal | `TyBool | `TyArr as typ ->
    let decl =
      Z3.FuncDecl.mk_const_decl z3 (z3_of_symbol z3 sym) (sort_of_typ z3 typ)
    in
    Z3.Expr.mk_const_f z3 decl
  | `TyFun _ -> invalid_arg "z3_const_of_symbol: not a first-order symbol"

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
    | `Atom (`Arith (`Eq, s, t)) ->
      begin
        let default () =
          Z3.Boolean.mk_eq z3 (of_arith_term s) (of_arith_term t)
        in
(*n        try
          match s with
          |
        with Linear.Nonlinear -> default ()
*)
        default ()
      end
    | `Atom (`Arith (`Leq, s, t)) -> Z3.Arithmetic.mk_le z3 (of_arith_term s) (of_arith_term t)
    | `Atom (`Arith (`Lt, s, t)) -> Z3.Arithmetic.mk_lt z3 (of_arith_term s) (of_arith_term t)
    | `Atom (`ArrEq (s, t)) -> Z3.Boolean.mk_eq z3 (of_arr_term s) (of_arr_term t)
    | `Proposition (`Var i) ->
      Z3.Quantifier.mk_bound z3 i (sort_of_typ z3 `TyBool)
    | `Atom (`IsInt s) ->
      begin
        let default () =
          Z3.Arithmetic.Real.mk_is_integer z3
            (z3_of_expr srk z3 (s :> ('a, typ_fo) expr))
        in
        try
          (* Z3 handles mod better than is_int, so translate to mod if
             possible. *)
          let lin = Linear.linterm_of srk s in
          let denom = Linear.QQVector.common_denominator lin in
          let t = Linear.QQVector.scalar_mul (QQ.of_zz denom) lin
                  |> Linear.of_linterm srk
          in
          (match expr_typ srk t with
           | `TyInt ->
             let d = Z3.Arithmetic.Integer.mk_numeral_s z3 (ZZ.show denom) in
             let t = z3_of_expr srk z3 (t :> ('a, typ_fo) expr) in
             Z3.Boolean.mk_eq z3
               (Z3.Arithmetic.Integer.mk_mod z3 t d)
               (Z3.Arithmetic.Integer.mk_numeral_i z3 0)
           | _ -> default ())
        with Linear.Nonlinear -> default ()
      end
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
    | `IsInt args ->
       (mk_and context
          (List.map (fun x -> x |> arith_term |> mk_is_int context) args) :> 'a gexpr)
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
  assert (Z3.Symbol.is_int_symbol sym);
  symbol_of_int (Z3.Symbol.get_int sym)

let term_of_z3 context term =
  match Expr.refine_coarse context (of_z3 context sym_of_decl term) with
  | `Term t -> t
  | _ -> invalid_arg "term_of"

let formula_of_z3 context phi =
  match Expr.refine context (of_z3 context sym_of_decl phi) with
  | `Formula phi -> phi
  |  _ -> invalid_arg "formula_of"

let expr_of_z3 context expr = of_z3 context sym_of_decl expr

type 'a solver =
  { srk : 'a context;
    z3 : z3_context;
    s : Z3.Solver.solver;
    formula_of : z3_expr -> 'a formula;
    of_formula : 'a formula -> z3_expr }

let get_default_context =
  let default_context = ref None in
  fun () ->
    match !default_context with
    | Some ctx -> ctx
    | None ->
      let ctx = Z3.mk_context [] in
      default_context := Some ctx;
      ctx

module Solver = struct
  type 'a t = 'a solver

  let make ?(context=get_default_context ()) ?(theory="") srk =
    let s =
      if theory = "" then
        Z3.Solver.mk_simple_solver context
      else
        Z3.Solver.mk_solver_s context theory
    in
    let of_formula = z3_of_formula srk context in
    let formula_of t = formula_of_z3 srk t in
    { srk; z3 = context; s; of_formula; formula_of }


  let add solver formulas =
    Z3.Solver.add solver.s (List.map solver.of_formula formulas)

  let push solver = Z3.Solver.push solver.s
  let pop solver = Z3.Solver.pop solver.s
  let reset solver = Z3.Solver.reset solver.s

  let check ?(assumptions=[]) solver =
    let args = List.map solver.of_formula assumptions in
    try
      match Log.time "solver.check" (Z3.Solver.check solver.s) args with
      | Z3.Solver.SATISFIABLE -> `Sat
      | Z3.Solver.UNSATISFIABLE -> `Unsat
      | Z3.Solver.UNKNOWN -> `Unknown
    with Z3.Error x ->
      logf ~level:`warn "Caught Z3 exception: %s" x;
      `Unknown


  let expr_of_sym srk z3 symbol =
    match typ_symbol srk symbol with
    | `TyReal | `TyInt | `TyBool -> z3_const_of_symbol srk z3 symbol
    | _ -> assert false

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
        | None ->
          logf "symbol: %a" (pp_symbol srk) sym;
          assert false

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

  let get_model ?(symbols=[]) ?(assumptions=[]) solver =
    let srk = solver.srk in
    let z3 = solver.z3 in
    match check ~assumptions solver with
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
    match check solver with
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
    match check ~assumptions solver with
    | `Sat -> `Sat
    | `Unknown -> `Unknown
    | `Unsat ->
      `Unsat (List.map solver.formula_of (Z3.Solver.get_unsat_core solver.s))

  let get_reason_unknown solver = Z3.Solver.get_reason_unknown solver.s
end

let optimize_box ?(context=get_default_context ()) srk phi objectives =
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

let load_smtlib2 ?(context=get_default_context ()) srk str =
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

let qe ?(context=get_default_context ()) srk phi =
  let open Z3 in
  let z3 = context in
  let solve = Tactic.mk_tactic z3 "qe" in
  let simpl = Tactic.mk_tactic z3 "simplify" in
  let qe = Tactic.and_then z3 solve simpl [] in
  let g = Goal.mk_goal z3 false false false in
  Goal.add g [z3_of_formula srk z3 phi];
  of_apply_result srk (Tactic.apply qe g None)

let simplify ?(context=get_default_context ()) srk phi =
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

  let mk_solver ?(context=get_default_context ()) srk =
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

(** CHC solving via Z3's Spacer Fixpoint engine.
    Note that this module is separate from the [CHC] module above 
    
    - In this module, both positive and negative results comes with artifacts:
      ([`Reachable]/[`Unreachable]/[`Unknown]). In case of a [`Reachable] answer,
      the solver returns a derivation tree representing the counterexample trace.
      In case of a [`Unreachable] answer, the solver returns a valuation for each
      relation symbol. The valuation is inductive w.r.t. that symbol. Each valuation
      is de Bruijn-encoded.
    - In this module, rules are specified as srk formulas over constant symbols and
      relation symbols, which are represented as srk functions to bool. 
      The caller must specify which symbols get universally quantified via
      [Z3.Quantifier.mk_forall_const].  
    - On a [`Reachable] answer, our code performs a traversal of the Spacer 
      refutation proof, which manifests as a tree of "hyper-resolution" steps.
      We then reconstruct a derivation of the counterexample by valuing the 
      relation's universally quantified variables in the proof tree.
       - we decide which symbols are relations are recognized by 
         looking them up in a table
       - for each derivation step, we construct a SMT query to value all 
         universally quantified variables in the rule through srk's SMT solver
         interface ([Solver], i.e. [Smt.StdSolver])
    - this solver reuses the default Z3 context via [get_default_context ()]
  *)
module FixedpointChc = struct
  type query_status = [ 
        `Reachable               (* represents a CHC query without a model but with a counterexample *)
      | `Unreachable             (* represents a CHC query with a model *)
      | `Unknown of string ]     (* represents a spacer failure *)

  (* A ground relation. Each ground relation is a symbol that is interpreted by a ground formula. *)
  type 'a relation_fact = {
    relation : symbol option;
    fact_args : (('a, typ_fo) expr) list;
    fact_raw : z3_expr;
  }

  (* A step in the derivation tree for CHC counterexamples. *)
  type 'a step = {
    step_index : int;                                 (* Position of the node in the trace *)
    rule_name : string option;                        (* Node name of the derivation tree *)
    conclusion : 'a relation_fact;                    (* The conclusion of the derivation step *)
    premises : 'a relation_fact list;                 (* The premises of the derivation step *)
    valuation : (symbol * ('a, typ_fo) expr) list;    (* The valuation of the universally quantified variables in the rule *)
    step_raw_rule : z3_expr;                          (* The raw rule in Z3 AST form *)
    step_status : [ `Ok | `Failed of string ];
  }

  type 'a query_answer = {
    status : query_status;
    raw_answer : z3_expr option;
    steps : 'a step list;
  }

  (* Metadata we associate with every rule at [add_rule] time.  The witness
     extractor replays proof steps against this stored (srk-level) copy of
     the rule, because the copy of the rule inside Z3's proof term is
     possibly rewritten by Z3 and would hav eits bound variables renamed, 
     so it cannot be used to recover srk symbol identities. *)
  type 'a rule_metadata = {
    rm_name : string option;
    rm_vars : symbol list;         (* quantified symbols, in binder order *)
    rm_body : 'a formula;          (* srk body, over constant symbols *)
    rm_head : 'a formula;          (* srk head atom, over constant symbols *)
    rm_head_rel : symbol;
    rm_body_rels : symbol list;    (* body relation multiset, sorted *)
    rm_z3 : z3_expr;               (* exact AST given to Z3 (id fast path) *)
  }

  (* representation of the Spacer solver object. *)
  type 'a solver = {
    srk : 'a context;
    z3 : z3_context;
    fp : Z3.Fixedpoint.fixedpoint;
    error : symbol;                          (* error() => false is the goal clause *)
    mutable relations : Symbol.Set.t;        (* collection of all registered relation symbols *)
    (* Z3 FuncDecl id -> srk relation symbol mapping.  
       We translate srk Functions to Z3 FuncDecls and we use this to maintain mapping info. *)
    decl_table : (int, symbol) Hashtbl.t;
    mutable rules : 'a rule_metadata list;       (* [rules] is a stack maintained in reverse insertion order *)
    mutable queried : bool;                      (* rules are frozen after the first query *)
  }

  type 'a t = 'a solver

  let register_relation solver rel =
    (match typ_symbol solver.srk rel with
     | `TyFun (_, `TyBool) -> ()
     | _ ->
       invalid_arg
         (Printf.sprintf
            "FixedpointChc.register_relation: cannot handle term : %s is not a relation \
             (expected type `TyFun (_, `TyBool))"
            (show_symbol solver.srk rel)));
    let decl = decl_of_symbol solver.z3 solver.srk rel in
    Z3.Fixedpoint.register_relation solver.fp decl;
    Hashtbl.replace solver.decl_table (Z3.FuncDecl.get_id decl) rel;
    solver.relations <- Symbol.Set.add rel solver.relations

  let mk_relation solver ?(name="R") dom =
    let rel = mk_symbol solver.srk ~name (`TyFun (dom, `TyBool)) in
    register_relation solver rel;
    rel

  let mk_solver ?(context=get_default_context ()) srk =
    let fp = Z3.Fixedpoint.mk_fixedpoint context in
    (* It's pretty important to ensure Spacer does not mutate the CHC relations
       so that we know what the relations look like during proof reconstruction.
       
       The arguments below try to disable a bunch of transformations
      on the input CHCs Z3 would be doing by default.

        - Disable the xform.* argument settings below stop Z3
       from slicing/inlining the rules before solving, making the resultant
       Z3 output parsable.

        - Disable tail_simplifier_pve which propagates variable equalities rules.
       leaving it enabled results in Z3 inlining small non-recursive systems into
       a single asserted query fact, which destroys the derivation. 
       
        - Disable subsumption_checker which also does inling of CHC rules for certain
        inputs. *)
    let params = Z3.Params.mk_params context in
    let sym x = Z3.Symbol.mk_string context x in
    Z3.Params.add_symbol params (sym "engine") (sym "spacer");
    Z3.Params.add_bool params (sym "xform.slice") false;
    Z3.Params.add_bool params (sym "xform.inline_linear") false;
    Z3.Params.add_bool params (sym "xform.inline_eager") false;
    Z3.Params.add_bool params (sym "xform.tail_simplifier_pve") false;
    Z3.Params.add_bool params (sym "xform.subsumption_checker") false;
    Z3.Fixedpoint.set_parameters fp params;
    (* distinguished error node *)
    let error = mk_symbol srk ~name:"chc_error" (`TyFun ([], `TyBool)) in
    let solver =
      { srk; z3 = context; fp; error;
        relations = Symbol.Set.empty;
        decl_table = Hashtbl.create 991;
        rules = [];
        queried = false }
    in
    register_relation solver error;
    solver

  let error_relation solver = solver.error

  let destruct_relation_application solver phi =
    match destruct solver.srk phi with
    | `App (rel, args) when Symbol.Set.mem rel solver.relations ->
      Some (rel, args)
    | _ -> None

  let is_relation_application solver phi =
    match destruct_relation_application solver phi with
    | Some _ -> true
    | None -> false

  (* Flatten nested conjunctions into a conjunct list ([true] vanishes). *)
  let rec flatten_nested_conjuncts srk phi acc =
    match Formula.destruct srk phi with
    | `And phis -> List.fold_right (fun c acc -> flatten_nested_conjuncts srk c acc) phis acc
    | `Tru -> acc
    | _ -> phi :: acc

  (* Split the body of a Horn clause rule into (relation applications, phi), where 
      phi is free of any relation symbols.  *)
  let split_body solver body =
    let atoms, pure =
      List.partition (is_relation_application solver) (flatten_nested_conjuncts solver.srk body [])
    in
    (atoms, pure)

  (* Type-check application of a relation symbol to make sure the call is well-typed. *)
  let typecheck_relation_application solver atom =
    match destruct_relation_application solver atom with
    | None -> assert false
    | Some (rel, args) ->
      let dom = match typ_symbol solver.srk rel with
        | `TyFun (dom, `TyBool) -> dom
        | _ -> assert false      (* guaranteed by register_relation *)
      in
      if List.length dom <> List.length args then
        invalid_arg
          (Printf.sprintf
             "FixedpointChc: relation symbol %s expects %d arguments but is \
              applied to %d arguments"
             (show_symbol solver.srk rel)
             (List.length dom)
             (List.length args));
      List.iter2 (fun expected arg ->
          let actual = expr_typ solver.srk arg in
          if actual <> (expected :> typ) then
            invalid_arg
              (Printf.sprintf
                 "FixedpointChc: ill-sorted argument to relation symbol %s"
                 (show_symbol solver.srk rel)))
        dom args

  (* A symbol may be universally quantified in a rule if it is a
     a constant that is not a registered relation.  *)
  let quantifiable solver s =
    not (Symbol.Set.mem s solver.relations)
    && (match typ_symbol solver.srk s with
        | `TyInt | `TyReal | `TyBool | `TyArr -> true
        | `TyFun _ -> false)

  (* Detect free variables to form the rule's quantified symbols list *)
  let quantified_vars solver ?vars body head =
    let occurring =
      Symbol.Set.filter
        (quantifiable solver)
        (Symbol.Set.union (symbols body) (symbols head))
    in
    match vars with
    | None -> Symbol.Set.elements occurring
    | Some vs ->
      let seen = ref Symbol.Set.empty in
      vs |> List.filter (fun s ->
          if Symbol.Set.mem s !seen then false
          else begin
            seen := Symbol.Set.add s !seen;
            Symbol.Set.mem s occurring
          end)

  let add_rule solver ?name ?vars ~body ~head () =
    if solver.queried then
      invalid_arg "FixedpointChc.add_rule: rules are frozen after a query";
    let srk = solver.srk in
    (* Normalize the head.  A head that is not a registered relation atom
       (including [mk_false]) is routed to the internal error relation:
       [body => head] becomes [body /\ not head => chc_error()].  This
       mirrors the convention of the older CHC module and lets callers state
       queries as [body => false]; query [error_relation solver] to check
       them. *)
    let body, head =
      match destruct_relation_application solver head with
      | Some _ -> body, head
      | None ->
        (mk_and srk [body; mk_not srk head], mk_app srk solver.error [])
    in
    match Formula.destruct srk body with
    | `Fls -> ()   
    | _ ->
      let atoms, _ = split_body solver body in
      List.iter (typecheck_relation_application solver) (head :: atoms);
      let vars = quantified_vars solver ?vars body head in
      let z3_matrix =
        (* A fact rule (body = true) is passed to Z3 as a bare head atom;
           otherwise as an implication. *)
        match Formula.destruct srk body with
        | `Tru -> z3_of_formula srk solver.z3 head
        | _ ->
          Z3.Boolean.mk_implies solver.z3
            (z3_of_formula srk solver.z3 body)
            (z3_of_formula srk solver.z3 head)
      in
      let z3_rule =
        (* Quantify rule-local symbols by abstracting the corresponding Z3
           constants.  Z3 rejects empty binder lists, so ground rules skip
           the quantifier. *)
        match vars with
        | [] -> z3_matrix
        | _ ->
          Z3.Quantifier.mk_forall_const solver.z3
            (List.map (z3_const_of_symbol srk solver.z3) vars)
            z3_matrix
            None [] [] None None
          |> Z3.Quantifier.expr_of_quantifier
      in
      let z3_name = BatOption.map (Z3.Symbol.mk_string solver.z3) name in
      Z3.Fixedpoint.add_rule solver.fp z3_rule z3_name;
      let head_rel = match destruct_relation_application solver head with
        | Some (rel, _) -> rel
        | None -> assert false
      in
      let body_rels =
        atoms
        |> List.map (fun atom ->
            match destruct_relation_application solver atom with
            | Some (rel, _) -> rel
            | None -> assert false)
        |> List.sort Stdlib.compare
      in
      solver.rules <-
        { rm_name = name; rm_vars = vars; rm_body = body; rm_head = head;
          rm_head_rel = head_rel; rm_body_rels = body_rels; rm_z3 = z3_rule }
        :: solver.rules

  let add solver phis =
    if solver.queried then
      invalid_arg "FixedpointChc.add: assertions are frozen after a query";
    Z3.Fixedpoint.add solver.fp
      (List.map (z3_of_formula solver.srk solver.z3) phis)


  module ProofWalk = struct
    (* The 'step' type represents a hyper-resolution node inside Spacer refutation, 
       [raw_rule]  : the rule corresponding to this node
       [raw_conclusion] : the ground fact derived by this node
       [raw_premises] : the ground facts required as assumptions by this node *)
    type raw_step = {
      raw_rule : z3_expr;
      raw_conclusion : z3_expr;
      raw_premises : z3_expr list;
    }

    let split_last xs =
      match List.rev xs with
      | [] -> failwith "split_last: empty list"
      | y :: ys -> (List.rev ys, y)

    let decl_name_opt e =
      try
        Some (Z3.Expr.get_func_decl e
              |> Z3.FuncDecl.get_name
              |> Z3.Symbol.to_string)
      with _ -> None

    let is_quantified_expr e = Z3.AST.is_quantifier (Z3.Expr.ast_of_expr e)

    let is_hyper_res_node e =
      match decl_name_opt e with
      | Some ("hyper-res" | "hyper-resolve" | "hyper_resolve") -> true
      | _ -> false

    (* Returns the premises of a proof tree node *)
    let premises_of (p: z3_expr) =
      if Z3.Proof.is_modus_ponens p || is_hyper_res_node p then
        fst (split_last (Z3.Expr.get_args p))
      else
        []

    (* The fact established by a proof node *)
    let proof_fact p =
      if Z3.Proof.is_asserted p || Z3.Proof.is_goal p
         || Z3.Proof.is_hypothesis p then
        match Z3.Expr.get_args p with
        | [fact] -> fact
        | _ -> p
      else if Z3.Proof.is_modus_ponens p || is_hyper_res_node p then
        snd (split_last (Z3.Expr.get_args p))
      else
        p

    let rec flatten_and e =
      if Z3.Boolean.is_and e then
        List.concat_map flatten_and (Z3.Expr.get_args e)
      else
        [e]

    (* Collect the hyper-resolution nodes of a proof in post-order: 
        for each step, the premises appear before it, and the conclusions follow it.
        the resulting list reads as a derivation (leaves first, query last). *)
    let walk_hyper_res_postorder proof =
      let seen = Hashtbl.create 31 in
      let out = ref [] in
      let rec visit p =
        let id = Z3.AST.get_id (Z3.Expr.ast_of_expr p) in
        if not (Hashtbl.mem seen id) then begin
          Hashtbl.add seen id ();
          List.iter visit (premises_of p);
          if is_hyper_res_node p then out := p :: !out
        end
      in
      visit proof;
      List.rev !out

    let raw_steps proof =
      walk_hyper_res_postorder proof
      |> BatList.filter_map (fun hr ->
          match Z3.Expr.get_args hr with
          | [] | [_] ->
            logf ~level:`warn
              "FixedpointChc: skipping malformed hyper-res node";
            None
          | args ->
            let premise_nodes, conclusion = split_last args in
            match premise_nodes with
            | main_rule :: side_proofs ->
              Some { raw_rule = proof_fact main_rule;
                     raw_conclusion = conclusion;
                     raw_premises = List.map proof_fact side_proofs }
            | [] -> None)

    (* ------------------------------------------------------------ *)
    (* Z3 fallback valuation
      RF June 26: The code below is created by Claude Code.
      When a proof step's rule cannot be matched against any stored rule
      we have no choice but to extract the result in raw Z3 format.
      Symbols inside these rules are extracted as Z3's bound-variable names
      , which cannot be mapped back to srk symbols.                 *)
    (* ------------------------------------------------------------ *)

    (* Peel the universal prefix of a rule as it appears in the proof. *)
    let decompose_horn_rule rule =
      let rec peel names sorts e =
        if is_quantified_expr e then
          let q = Z3.Quantifier.quantifier_of_expr e in
          if Z3.Quantifier.is_universal q then
            let names' =
              Z3.Quantifier.get_bound_variable_names q
              |> List.map Z3.Symbol.to_string
            in
            let sorts' = Z3.Quantifier.get_bound_variable_sorts q in
            peel (names @ names') (sorts @ sorts') (Z3.Quantifier.get_body q)
          else
            (names, sorts, e)
        else
          (names, sorts, e)
      in
      let names, sorts, core = peel [] [] rule in
      if Z3.Boolean.is_implies core then
        match Z3.Expr.get_args core with
        | [body; head] -> (names, sorts, head, flatten_and body)
        | _ -> (names, sorts, core, [])
      else
        (names, sorts, core, [])

    (* At the Z3 level, a relation symbol is a Bool-sorted application of an
       uninterpreted function declaration.  *)
    let is_relation_symbol z3 e =
      (not (is_quantified_expr e))
      && Z3.Sort.equal (Z3.Expr.get_sort e) (Z3.Boolean.mk_sort z3)
      && (try
            Z3.FuncDecl.get_decl_kind (Z3.Expr.get_func_decl e)
            = Z3enums.OP_UNINTERPRETED
          with _ -> false)

    let same_relation a b =
      Z3.FuncDecl.equal (Z3.Expr.get_func_decl a) (Z3.Expr.get_func_decl b)
      && Z3.Expr.get_num_args a = Z3.Expr.get_num_args b


    let instantiate_bound_vars e witnesses =
      Z3.Expr.substitute_vars e (List.rev witnesses)

    let matchings same relation_symbols facts =
      let rec go available facts =
        match facts with
        | [] -> if available = [] then [[]] else []
        | f :: rest ->
          available
          |> List.concat_map (fun (i, a) ->
              if same a f then
                go (List.remove_assoc i available) rest
                |> List.map (fun m -> (a, f) :: m)
              else
                [])
      in
      go (List.mapi (fun i a -> (i, a)) relation_symbols) facts

    let solve_step_valuation z3 rule conclusion premises =
      let names, sorts, head, body_lits = decompose_horn_rule rule in
      let witnesses =
        List.mapi
          (fun i s -> Z3.Expr.mk_fresh_const z3 (Printf.sprintf "__w%d_" i) s)
          sorts
      in
      let head_i = instantiate_bound_vars head witnesses in
      let body_i = List.map (fun l -> instantiate_bound_vars l witnesses) body_lits in
      let rel_atoms = List.filter (is_relation_symbol z3) body_i in
      let pure = List.filter (fun e -> not (is_relation_symbol z3 e)) body_i in
      let atom_eqs pat grd =
        (* Constraints forcing an instantiated relation symbol to equal a ground fact:
           pointwise argument equalities when both are relation atoms of the
           same declaration; plain equality otherwise. *)
        if is_relation_symbol z3 pat && is_relation_symbol z3 grd then
          if not (same_relation pat grd) then None
          else if Z3.Expr.get_num_args pat = 0 then
            Some [Z3.Boolean.mk_eq z3 pat grd]
          else
            Some (List.map2 (Z3.Boolean.mk_eq z3)
                    (Z3.Expr.get_args pat) (Z3.Expr.get_args grd))
        else
          Some [Z3.Boolean.mk_eq z3 pat grd]
      in
      match atom_eqs head_i conclusion with
      | None -> Error "rule head does not match proof conclusion"
      | Some head_eqs ->
        let try_matching pairs =
          let s = Z3.Solver.mk_simple_solver z3 in
          try
            Z3.Solver.add s head_eqs;
            List.iter (fun (pat, grd) ->
                match atom_eqs pat grd with
                | Some cs -> Z3.Solver.add s cs
                | None -> raise Exit)
              pairs;
            Z3.Solver.add s pure;
            match Z3.Solver.check s [] with
            | Z3.Solver.SATISFIABLE ->
              begin match Z3.Solver.get_model s with
                | None -> None
                | Some m ->
                  let value_of w =
                    match Z3.Model.eval m w true with
                    | Some v -> Z3.Expr.simplify v None
                    | None -> w
                  in
                  Some (List.map2
                          (fun nm w -> (nm, Z3.Expr.to_string (value_of w)))
                          names witnesses)
              end
            | _ -> None
          with Exit -> None
        in
        let rec first = function
          | [] -> Error "no consistent premise matching at the Z3 level"
          | m :: rest ->
            match try_matching m with
            | Some v -> Ok v
            | None -> first rest
        in
        first (matchings same_relation rel_atoms premises)
  end

  (* ---------------------------------------------------------------- *)
  (* Witness extraction (srk level)                                   *)
  (* [RF June 2026: The module below is largely coded with help of
      Claude Code. The main idea is that we perform a walk of Z3's
      Spacer proof tree, which consists of many hyper-resolution nodes,
      and then extract valuations for universally quantified symbols in
      each proof tree node (which corresponds to a node in counterexample
      hyper-path).                                                    *)
  (* ---------------------------------------------------------------- *)

  (* Recognize a declaration appearing in a proof term as one of our
     registered relations.  Primary key: Z3 FuncDecl id (decls are
     hash-consed per context).  Fallback: srk symbols become Z3 *int*
     symbols, so a decl whose name is an int symbol can be decoded
     directly.  Foreign declarations (e.g. Z3-generated [query!N], whose
     names are strings) return None -- they must never reach
     [sym_of_decl], which asserts int-symbol names. *)
  let lookup_decl solver decl =
    match Hashtbl.find_opt solver.decl_table (Z3.FuncDecl.get_id decl) with
    | Some rel -> Some rel
    | None ->
      let name = Z3.FuncDecl.get_name decl in
      if Z3.Symbol.is_int_symbol name then
        let s = symbol_of_int (Z3.Symbol.get_int name) in
        if Symbol.Set.mem s solver.relations then Some s else None
      else
        None

  (* Convert a ground fact from the proof into srk terms.  Total: any
     failure (foreign declaration, unconvertible argument, non-application
     expression) degrades to [relation = None] / [fact_args = []] with the
     raw Z3 expression preserved. *)
  let fact_of_z3 solver e =
    try
      let decl = Z3.Expr.get_func_decl e in
      match lookup_decl solver decl with
      | Some rel ->
        let fact_args =
          try List.map (expr_of_z3 solver.srk) (Z3.Expr.get_args e)
          with _ -> []
        in
        { relation = Some rel; fact_args; fact_raw = e }
      | None -> { relation = None; fact_args = []; fact_raw = e }
    with _ -> { relation = None; fact_args = []; fact_raw = e }

  (* Type-directed equality between two srk expressions of the same
     first-order type (used to equate rule-atom arguments with ground fact
     arguments). *)
  let mk_eq_typed srk a b =
    match Expr.refine srk a, Expr.refine srk b with
    | `ArithTerm a, `ArithTerm b -> mk_eq srk a b
    | `ArrTerm a, `ArrTerm b -> mk_arr_eq srk a b
    | `Formula a, `Formula b -> mk_iff srk a b
    | _, _ -> invalid_arg "FixedpointChc: ill-typed argument equality"

  exception Unconverted

  let fact_rel_args solver fact =
    match fact.relation with
    | None -> raise Unconverted
    | Some rel ->
      let arity = match typ_symbol solver.srk rel with
        | `TyFun (dom, _) -> List.length dom
        | _ -> 0
      in
      if List.length fact.fact_args = arity then (rel, fact.fact_args)
      else raise Unconverted

  (* Solve one derivation step against a candidate stored rule: find values
     for the rule's quantified symbols under which the rule's head equals
     the step's conclusion, its body atoms equal the step's premises (for
     some matching), and its pure constraints hold.  The satisfiability
     query goes through srk's standard SMT solver interface ([Solver] =
     [Smt.StdSolver]); using the engine's Z3 context.  On success the
     valuation is keyed by the rule's own srk symbols. *)
  let solve_step solver rm conclusion premises =
    let srk = solver.srk in
    try
      let (concl_rel, concl_args) = fact_rel_args solver conclusion in
      let prems = List.map (fact_rel_args solver) premises in
      if rm.rm_head_rel <> concl_rel then
        Error "head relation does not match conclusion"
      else begin
        let atoms, pure = split_body solver rm.rm_body in
        let atom_pairs =
          List.map (fun atom ->
              match destruct_relation_application solver atom with
              | Some p -> p
              | None -> assert false)
            atoms
        in
        let head_args =
          match destruct_relation_application solver rm.rm_head with
          | Some (_, args) -> args
          | None -> assert false
        in
        let head_eqs = List.map2 (mk_eq_typed srk) head_args concl_args in
        (* Interpretation cannot represent array values, so array-typed
           symbols are omitted from the model request (and hence from the
           valuation). *)
        let model_syms =
          List.filter (fun s ->
              match typ_symbol srk s with
              | `TyArr -> false
              | _ -> true)
            rm.rm_vars
        in
        let try_matching pairing =
          let prem_eqs =
            List.concat_map
              (fun ((_, atom_args), (_, fact_args)) ->
                 List.map2 (mk_eq_typed srk) atom_args fact_args)
              pairing
          in
          let phi = mk_and srk (head_eqs @ prem_eqs @ pure) in
          let aux = Solver.make ~context:solver.z3 srk in
          Solver.add aux [phi];
          match Solver.get_concrete_model aux model_syms with
          | `Sat interp ->
            Some (model_syms |> List.map (fun s ->
                let value : ('a, typ_fo) expr =
                  match Interpretation.value interp s with
                  | `Real qq -> ((mk_real srk qq) :> ('a, typ_fo) expr)
                  | `Bool true -> ((mk_true srk) :> ('a, typ_fo) expr)
                  | `Bool false -> ((mk_false srk) :> ('a, typ_fo) expr)
                  | `Fun _ -> mk_const srk s   (* not expected for
                                                  first-order symbols *)
                in
                (s, value)))
          | `Unsat | `Unknown -> None
        in
        let same (rel_a, _) (rel_f, _) = rel_a = rel_f in
        let rec first = function
          | [] -> Error "no consistent premise matching"
          | m :: rest ->
            match try_matching m with
            | Some v -> Ok v
            | None -> first rest
        in
        first (ProofWalk.matchings same atom_pairs prems)
      end
    with Unconverted -> Error "step facts are not convertible to srk"

  (* Candidate stored rules for a proof step: same head relation and same
     multiset of body relations.  If the proof cites a rule AST that is
     literally one of ours (Z3 did not rewrite it), that rule is moved to
     the front. *)
  let candidate_rules solver raw_rule concl_rel prem_rels =
    let prem_key = List.sort Stdlib.compare prem_rels in
    let structural =
      List.filter
        (fun rm -> rm.rm_head_rel = concl_rel && rm.rm_body_rels = prem_key)
        solver.rules
    in
    let raw_id = Z3.AST.get_id (Z3.Expr.ast_of_expr raw_rule) in
    let exact, rest =
      List.partition
        (fun rm -> Z3.AST.get_id (Z3.Expr.ast_of_expr rm.rm_z3) = raw_id)
        structural
    in
    exact @ rest

  let extract_steps solver answer =
    ProofWalk.raw_steps answer
    |> List.map (fun (rs : ProofWalk.raw_step) ->
        let conclusion = fact_of_z3 solver rs.ProofWalk.raw_conclusion in
        let premises =
          List.map (fact_of_z3 solver) rs.ProofWalk.raw_premises
        in
        (* Diagnostic-only fallback: the prototype's Z3-level valuation.
           Its variable names are Z3's (renamed) bound-variable names, so
           the result is reported as a string, not as a typed valuation. *)
        let fallback_message () =
          match
            ProofWalk.solve_step_valuation solver.z3
              rs.ProofWalk.raw_rule
              rs.ProofWalk.raw_conclusion
              rs.ProofWalk.raw_premises
          with
          | Ok vals ->
            Printf.sprintf
              "rule not identified; Z3-level valuation: %s"
              (String.concat ", "
                 (List.map (fun (n, v) -> n ^ " = " ^ v) vals))
          | Error msg ->
            Printf.sprintf
              "rule not identified; Z3-level fallback failed: %s" msg
        in
        let identified =
          match conclusion.relation with
          | None -> None
          | Some concl_rel ->
            let prem_rels_opt =
              try
                Some (List.map (fun p ->
                    match p.relation with
                    | Some r -> r
                    | None -> raise Unconverted)
                    premises)
              with Unconverted -> None
            in
            match prem_rels_opt with
            | None -> None
            | Some prem_rels ->
              let rec try_candidates = function
                | [] -> None
                | rm :: rest ->
                  match solve_step solver rm conclusion premises with
                  | Ok valuation -> Some (rm, valuation)
                  | Error _ -> try_candidates rest
              in
              try_candidates
                (candidate_rules solver rs.ProofWalk.raw_rule
                   concl_rel prem_rels)
        in
        let rule_name, valuation, step_status =
          match identified with
          | Some (rm, valuation) -> (rm.rm_name, valuation, `Ok)
          | None -> (None, [], `Failed (fallback_message ()))
        in
        { step_index = 0; rule_name; conclusion; premises; valuation;
          step_raw_rule = rs.ProofWalk.raw_rule; step_status })
    (* Z3 closes the derivation with a synthetic step concluding an
       internal query relation (e.g. [query!N]) from the queried fact.
       Steps whose conclusion cannot be mapped to a registered relation
       carry no client-visible information, so they are dropped from the
       typed derivation; the raw answer retains them for debugging. *)
    |> List.filter (fun st ->
        match st.conclusion.relation with
        | Some _ -> true
        | None ->
          logf ~level:`debug
            "FixedpointChc: dropping synthetic derivation step %s"
            (Z3.Expr.to_string st.conclusion.fact_raw);
          false)
    |> List.mapi (fun i st -> { st with step_index = i })

  let query_relation solver rel =
    if not (Symbol.Set.mem rel solver.relations) then
      invalid_arg "FixedpointChc.query_relation: unregistered relation";
    solver.queried <- true;
    let decl = decl_of_symbol solver.z3 solver.srk rel in
    let status =
      try
        (* query_r queries the registered declaration directly; unlike
           [query] on a formula it does not manufacture an auxiliary
           [query!N] relation for the goal. *)
        match Z3.Fixedpoint.query_r solver.fp [decl] with
        | Z3.Solver.SATISFIABLE -> `Reachable
        | Z3.Solver.UNSATISFIABLE -> `Unreachable
        | Z3.Solver.UNKNOWN ->
          let reason =
            try Z3.Fixedpoint.get_reason_unknown solver.fp
            with Z3.Error msg -> msg
          in
          `Unknown reason
      with Z3.Error msg ->
        logf ~level:`warn "FixedpointChc.query_relation: Z3 error: %s" msg;
        `Unknown msg
    in
    let raw_answer =
      match status with
      | `Reachable ->
        (try Z3.Fixedpoint.get_answer solver.fp with Z3.Error _ -> None)
      | _ -> None
    in
    let steps =
      match raw_answer with
      | Some answer ->
        (try extract_steps solver answer
         with exn ->
           logf ~level:`warn
             "FixedpointChc: witness extraction failed: %s"
             (Printexc.to_string exn);
           [])
      | None -> []
    in
    { status; raw_answer; steps }

  let get_solution solver rel =
    if not (Symbol.Set.mem rel solver.relations) then
      invalid_arg "FixedpointChc.get_solution: unregistered relation";
    if List.exists (fun rm -> rm.rm_head_rel = rel) solver.rules then
      let decl = decl_of_symbol solver.z3 solver.srk rel in
      match Z3.Fixedpoint.get_cover_delta solver.fp (-1) decl with
      | Some inv -> formula_of_z3 solver.srk inv
      | None -> failwith "FixedpointChc.get_solution: no solution available"
    else
      (* A relation that heads no rule is empty. *)
      mk_false solver.srk

  (* Print the CHC system  *)
  let pp_rules formatter solver =
    let srk = solver.srk in
    let pp_rule formatter rm =
      Format.fprintf formatter "@[<hov 2>";
      (match rm.rm_name with
       | Some name -> Format.fprintf formatter "%s: " name
       | None -> ());
      (match rm.rm_vars with
       | [] -> ()
       | vars ->
         Format.fprintf formatter "forall %a.@ "
           (SrkUtil.pp_print_enum_nobox (pp_symbol srk))
           (BatList.enum vars));
      Format.fprintf formatter "%a@ => %a@]"
        (Formula.pp srk) rm.rm_body
        (Formula.pp srk) rm.rm_head
    in
    Format.fprintf formatter "@[<v 0>%a@]"
      (SrkUtil.pp_print_enum_nobox
         ~pp_sep:(fun formatter () -> Format.fprintf formatter "@;")
         pp_rule)
      (BatList.enum (List.rev solver.rules))

  let pp_fact solver formatter fact =
    match fact.relation with
    | Some rel ->
      Format.fprintf formatter "@[<h>%a(%a)@]"
        (pp_symbol solver.srk) rel
        (SrkUtil.pp_print_enum_nobox (Expr.pp solver.srk))
        (BatList.enum fact.fact_args)
    | None ->
      (* Foreign fact (e.g. a Z3-internal relation): show the raw expr. *)
      Format.pp_print_string formatter (Z3.Expr.to_string fact.fact_raw)

  let pp_step solver formatter step =
    let srk = solver.srk in
    Format.fprintf formatter "@[<v 2>step %d" step.step_index;
    (match step.rule_name with
     | Some name -> Format.fprintf formatter " [%s]" name
     | None -> ());
    Format.fprintf formatter ": %a" (pp_fact solver) step.conclusion;
    (match step.premises with
     | [] -> ()
     | premises ->
       Format.fprintf formatter "@;<- @[<hov 0>%a@]"
         (SrkUtil.pp_print_enum_nobox (pp_fact solver))
         (BatList.enum premises));
    begin match step.step_status with
      | `Ok ->
        if step.valuation <> [] then
          Format.fprintf formatter "@;with @[<hov 0>%a@]"
            (SrkUtil.pp_print_enum_nobox
               (fun formatter (sym, value) ->
                  Format.fprintf formatter "@[<h>%a = %a@]"
                    (pp_symbol srk) sym
                    (Expr.pp srk) value))
            (BatList.enum step.valuation)
      | `Failed msg -> Format.fprintf formatter "@;FAILED: %s" msg
    end;
    Format.fprintf formatter "@]"

  let pp_derivation solver formatter steps =
    Format.fprintf formatter "@[<v 0>%a@]"
      (SrkUtil.pp_print_enum_nobox
         ~pp_sep:(fun formatter () -> Format.fprintf formatter "@;")
         (pp_step solver))
      (BatList.enum steps)

  let to_string solver = Z3.Fixedpoint.to_string solver.fp
end

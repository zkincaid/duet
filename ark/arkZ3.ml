open Syntax
open BatPervasives

include Log.Make(struct let name = "ark.arkZ3" end)

exception Unknown_result

type expr = Z3.Expr.expr
type func_decl = Z3.FuncDecl.func_decl
type sort = Z3.Sort.sort

type 'a open_expr = [
  | `Real of QQ.t
  | `App of func_decl * 'a list
  | `Var of int * typ_fo
  | `Add of 'a list
  | `Mul of 'a list
  | `Binop of [ `Div | `Mod ] * 'a * 'a
  | `Unop of [ `Floor | `Neg ] * 'a
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

let int_val x = Z3.Arithmetic.Integer.get_int x

let zz_val ast = ZZ.of_string (Z3.Arithmetic.Integer.numeral_to_string ast)

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
  | _ -> invalid_arg "typ_of_sort"

let sort_of_typ z3 = function
  | `TyInt -> Z3.Arithmetic.Integer.mk_sort z3
  | `TyReal -> Z3.Arithmetic.Real.mk_sort z3
  | `TyBool -> Z3.Boolean.mk_sort z3

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

let mk_quantifier_simplify_tactic z3 =
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

class type ['a] z3_context = object
  method ark : 'a context
  method z3 : Z3.context
  method mk_solver : unit -> 'a smt_solver

  method of_term : 'a term -> Z3.Expr.expr
  method of_formula : 'a formula -> Z3.Expr.expr
  method term_of : Z3.Expr.expr -> 'a term
  method formula_of : Z3.Expr.expr -> 'a formula

  method implies : 'a formula -> 'a formula -> bool
  method equiv : 'a formula -> 'a formula -> bool
  method is_sat : 'a formula -> [ `Sat | `Unsat | `Unknown ]
  method qe_sat : 'a formula -> [ `Sat | `Unsat | `Unknown ]
  method qe : 'a formula -> 'a formula
  method get_model : 'a formula -> [ `Sat of 'a smt_model | `Unsat | `Unknown ]
  method interpolate_seq : 'a formula list ->
    [ `Sat of 'a smt_model | `Unsat of 'a formula list | `Unknown ]
  method optimize_box : 'a formula -> 'a term list -> [ `Sat of Interval.t list
                                                      | `Unsat
                                                      | `Unknown ]
  method load_smtlib2 : string -> 'a formula
end

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

let decl_of_symbol z3 ark sym =
  let (param_sorts, return_sort) = match typ_symbol ark sym with
    | `TyInt | `TyReal | `TyBool ->
      invalid_arg "decl_of_symbol: not a function symbol"
    | `TyFun (params, return) ->
      (List.map (sort_of_typ z3) params, sort_of_typ z3 return)
  in
  let z3sym = z3_of_symbol z3 sym in
  Z3.FuncDecl.mk_func_decl z3 z3sym param_sorts return_sort

let rec z3_of_expr ark z3 expr =
  match refine ark expr with
  | `Term t -> z3_of_term ark z3 t
  | `Formula phi -> z3_of_formula ark z3 phi

and z3_of_term (ark : 'a context) z3 (term : 'a term) =
  let alg = function
    | `Real qq ->
      begin match QQ.to_zz qq with
        | Some zz -> Z3.Arithmetic.Integer.mk_numeral_s z3 (ZZ.show zz)
        | None -> Z3.Arithmetic.Real.mk_numeral_s z3 (QQ.show qq)
      end
    | `App (sym, []) ->
      let sort = match typ_symbol ark sym with
        | `TyInt -> sort_of_typ z3 `TyInt
        | `TyReal -> sort_of_typ z3 `TyReal
        | `TyBool | `TyFun (_,_) -> invalid_arg "z3_of.term: ill-typed application"
      in
      let decl = Z3.FuncDecl.mk_const_decl z3 (z3_of_symbol z3 sym) sort in
      Z3.Expr.mk_const_f z3 decl

    | `App (func, args) ->
      let decl = decl_of_symbol z3 ark func in
      Z3.Expr.mk_app z3 decl (List.map (z3_of_expr ark z3) args)

    | `Var (i, `TyFun (_, _)) | `Var (i, `TyBool) -> invalid_arg "z3_of.term: variable"
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
    | `Ite (cond, bthen, belse) ->
      Z3.Boolean.mk_ite z3 (z3_of_formula ark z3 cond) bthen belse
  in
  Term.eval ark alg term

and z3_of_formula ark z3 phi =
  let of_term = z3_of_term ark z3 in
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
    | `Atom (`Eq, s, t) -> Z3.Boolean.mk_eq z3 (of_term s) (of_term t)
    | `Atom (`Leq, s, t) -> Z3.Arithmetic.mk_le z3 (of_term s) (of_term t)
    | `Atom (`Lt, s, t) -> Z3.Arithmetic.mk_lt z3 (of_term s) (of_term t)
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
      let decl = decl_of_symbol z3 ark predicate in
      Z3.Expr.mk_app z3 decl (List.map (z3_of_expr ark z3) args)
    | `Ite (cond, bthen, belse) -> Z3.Boolean.mk_ite z3 cond bthen belse
  in
  Formula.eval ark alg phi

type 'a gexpr = ('a, typ_fo) Syntax.expr
let of_z3 context sym_of_decl expr =
  let term expr =
    match refine context expr with
    | `Term t -> t
    | _ -> invalid_arg "of_z3.term"
  in
  let formula expr =
    match refine context expr with
    | `Formula phi -> phi
    | _ -> invalid_arg "of_z3.formula"
  in
  let alg : (('a, typ_fo) Syntax.expr) open_expr -> ('a, typ_fo) Syntax.expr =
    function
    | `Real qq -> (mk_real context qq :> 'a gexpr)
    | `Var (i, typ) -> mk_var context i typ
    | `App (decl, args) ->
      let const_sym = sym_of_decl decl in
      mk_app context const_sym args
    | `Add sum -> (mk_add context (List.map term sum) :> 'a gexpr)
    | `Mul product -> (mk_mul context (List.map term product) :> 'a gexpr)
    | `Binop (`Div, s, t) -> (mk_div context (term s) (term t) :> 'a gexpr)
    | `Binop (`Mod, s, t) -> (mk_mod context (term s) (term t) :> 'a gexpr)
    | `Unop (`Floor, t) -> (mk_floor context (term t) :> 'a gexpr)
    | `Unop (`Neg, t) -> (mk_neg context (term t) :> 'a gexpr)
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
      begin match refine context s, refine context t with
        | `Term s, `Term t -> (mk_eq context s t :> 'a gexpr)
        | `Formula phi, `Formula psi ->
          (mk_or context [mk_and context [phi; psi];
                          mk_and context [mk_not context phi;
                                          mk_not context psi]]
           :> 'a gexpr)
        | _, _ -> invalid_arg "of_z3: equal"
      end
    | `Atom (`Leq, s, t) -> (mk_leq context (term s) (term t) :> 'a gexpr)
    | `Atom (`Lt, s, t) -> (mk_lt context (term s) (term t) :> 'a gexpr)
    | `Ite (cond, bthen, belse) -> mk_ite context (formula cond) bthen belse
  in
  eval alg expr

(* sym_of_decl is sufficient for round-tripping, since ark symbols become
   Z3 int symbols *)
let sym_of_decl decl =
  let sym = Z3.FuncDecl.get_name decl in
  assert (Z3.Symbol.is_int_symbol sym);
  symbol_of_int (Z3.Symbol.get_int sym)

let term_of_z3 context term =
  match refine context (of_z3 context sym_of_decl term) with
  | `Term t -> t
  | _ -> invalid_arg "term_of"

let formula_of_z3 context phi =
  match refine context (of_z3 context sym_of_decl phi) with
  | `Formula phi -> phi
  |  _ -> invalid_arg "formula_of"


class ['a] z3_model (ark : 'a context) z3 m =
  let of_formula = z3_of_formula ark z3 in
  let of_term = z3_of_term ark z3 in
  object(self)
    method eval_int term =
      match Z3.Model.eval m (of_term term) true with
      | Some x -> zz_val x
      | None -> invalid_arg "eval_int: not an integer term"

    method eval_real term =
      match Z3.Model.eval m (of_term term) true with
      | Some x -> qq_val x
      | None -> invalid_arg "eval_real: not a real term"

    method sat phi =
      match Z3.Model.eval m (of_formula phi) true with
      | Some x -> bool_val x
      | None -> assert false

    method eval_fun func =
      let decl = decl_of_symbol z3 ark func in
      let formals = match typ_symbol ark func with
        | `TyFun (params, _) ->
          List.mapi (fun i typ -> mk_var ark i typ) params
        | _ -> invalid_arg "eval_fun: not a function"
      in
      match Z3.Model.get_func_interp m decl with
      | None -> assert false
      | Some interp ->
        let default =
          of_z3 ark sym_of_decl
            (Z3.Model.FuncInterp.get_else interp)
        in
        let mk_eq x y = (* type-generic equality *)
          match refine ark x, refine ark y with
          | `Term x, `Term y ->
            (mk_eq ark x y :> ('a, 'typ_fo) Syntax.expr)
          | `Formula x, `Formula y ->
            (mk_iff ark x y :> ('a, 'typ_fo) Syntax.expr)
          | _, _ -> assert false
        in
        List.fold_right (fun entry rest ->
            let value =
              Z3.Model.FuncInterp.FuncEntry.get_value entry
              |> of_z3 ark sym_of_decl
            in
            let cond =
              List.map2 (fun formal value ->
                  mk_eq formal (of_z3 ark sym_of_decl value))
                formals
                (Z3.Model.FuncInterp.FuncEntry.get_args entry)
              |> mk_and ark
            in
            mk_ite ark cond value rest)
          (Z3.Model.FuncInterp.get_entries interp)
          default

    method to_string () = Z3.Model.to_string m
  end

class ['a] z3_solver (context : 'a context) z3 s =
  let of_formula = z3_of_formula context z3 in
  let formula_of = formula_of_z3 context in
  object(self)
    method add phis = Z3.Solver.add s (List.map of_formula phis)
    method push () = Z3.Solver.push s
    method pop = Z3.Solver.pop s
    method reset () = Z3.Solver.reset s

    method check args =
      let res =
        Log.time "solver.check" (Z3.Solver.check s) (List.map of_formula args)
      in
      match res with
      | Z3.Solver.SATISFIABLE -> `Sat
      | Z3.Solver.UNSATISFIABLE -> `Unsat
      | Z3.Solver.UNKNOWN -> `Unknown

    method get_model : unit -> [ `Sat of 'a smt_model | `Unsat | `Unknown ] =
      fun () ->
        match self#check [] with
        | `Sat ->
          begin match Z3.Solver.get_model s with
            | Some m -> `Sat (new z3_model context z3 m)
            | None -> `Unknown
          end
        | `Unsat -> `Unsat
        | `Unknown -> `Unknown

    method to_string () = Z3.Solver.to_string s

    method get_unsat_core : 'a formula list -> [ `Sat | `Unsat of ('a formula list) | `Unknown ]
      = 
      fun assumptions ->
        match self#check assumptions with
        | `Sat -> `Sat
        | `Unknown -> `Unknown
        | `Unsat ->
          `Unsat (List.map formula_of (Z3.Solver.get_unsat_core s))
  end

let mk_context : 'a context -> (string * string) list -> 'a z3_context
  = fun context opts ->
    let z3 = Z3.mk_context opts in
    let of_term = z3_of_term context z3 in
    let of_formula = z3_of_formula context z3 in
    let term_of = term_of_z3 context in
    let formula_of = formula_of_z3 context in
    let of_goal g =
      let open Z3 in
      List.map formula_of (Goal.get_formulas g)
      |> mk_and context
    in
    let of_apply_result result =
      let open Z3 in
      List.map of_goal (Tactic.ApplyResult.get_subgoals result)
      |> mk_and context
    in
    object (self)
      method ark = context
      method z3 = z3
      method of_term = of_term
      method of_formula = of_formula
      method term_of = term_of
      method formula_of = formula_of
      method mk_solver () =
        new z3_solver context z3 (Z3.Solver.mk_simple_solver z3)

      method is_sat phi =
        let s = self#mk_solver () in
        s#add [phi];
        s#check []

      method get_model phi =
        let s = self#mk_solver () in
        s#add [phi];
        s#get_model ()

      method implies phi psi =
        let s = self#mk_solver () in
        s#add [phi; mk_not context psi];
        match s#check [] with
        | `Sat -> false
        | `Unsat -> true
        | `Unknown -> raise Unknown_result

      method equiv phi psi =
        let s = self#mk_solver () in
        s#add [mk_or context [
            mk_and context [phi; mk_not context psi];
            mk_and context [psi; mk_not context phi]
          ]];
        match s#check [] with
        | `Sat -> false
        | `Unsat -> true
        | `Unknown -> raise Unknown_result

      method qe phi =
        let open Z3 in
        let solve = Tactic.mk_tactic z3 "qe" in
        let simpl = Tactic.mk_tactic z3 "simplify" in
        let qe = Tactic.and_then z3 solve simpl [] in
        let g = Goal.mk_goal z3 false false false in
        Goal.add g [of_formula phi];
        of_apply_result (Tactic.apply qe g None)

      method qe_sat phi =
        let open Z3 in
        let solve = Tactic.mk_tactic z3 "qsat" in
        let simpl = Tactic.mk_tactic z3 "simplify" in
        let qe = Tactic.and_then z3 solve simpl [] in
        let g = Goal.mk_goal z3 false false false in
        Goal.add g [of_formula phi];
        self#is_sat (of_apply_result (Tactic.apply qe g None))

      method interpolate_seq seq =
        let rec make_pattern phi = function
          | [psi] ->
            Z3.Boolean.mk_and z3 [
              Z3.Interpolation.mk_interpolant z3 phi;
              of_formula psi
            ]
          | psi::rest ->
            make_pattern
              (Z3.Boolean.mk_and z3 [
                  Z3.Interpolation.mk_interpolant z3 phi;
                  of_formula psi
                ])
              rest
          | [] ->
            invalid_arg "interpolate_seq: input sequence must be of length >= 2"
        in
        let params = Z3.Params.mk_params z3 in
        let pattern =
          if seq = [] then
            invalid_arg "interpolate_seq: input sequence must be of length >= 2";
          make_pattern (of_formula (List.hd seq)) (List.tl seq)
        in
        match Z3.Interpolation.compute_interpolant z3 pattern params with
        | (_, Some interp, None) -> `Unsat (List.map formula_of interp)
        | (_, None, Some m) -> `Sat (new z3_model context z3 m)
        | (_, _, _) -> `Unknown

      method optimize_box phi terms =
        let open Z3.Optimize in
        let opt = mk_opt z3 in
        let params = Z3.Params.mk_params z3 in
        let sym = Z3.Symbol.mk_string z3 in
        Z3.Params.add_symbol params (sym ":opt.priority") (sym "box");
        set_parameters opt params;
        add opt [of_formula phi];
        let mk_handles t =
          let z3t = of_term t in
          (minimize opt z3t, maximize opt z3t)
        in
        let handles = List.map mk_handles terms in
        let mk_interval (lo, hi) =
          let lower =
            let lo = get_lower lo in
            if Z3.Expr.is_numeral lo then
              Some (qq_val lo)
            else if Z3.Expr.to_string lo = "(* (- 1) oo)" then
              None
            else if Z3.Arithmetic.is_add lo then
              (* x + epsilon *)
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
            else if Z3.Arithmetic.is_add hi then
              (* x - epsilon *)
              Some (qq_val (List.hd (Z3.Expr.get_args hi)))
            else
              Log.fatalf "Smt.optimize_box: %s" (Z3.Expr.to_string hi)
          in
          Interval.make lower upper
        in
        match check opt with
        | Z3.Solver.SATISFIABLE -> `Sat (List.map mk_interval handles)
        | Z3.Solver.UNSATISFIABLE -> `Unsat
        | Z3.Solver.UNKNOWN -> `Unknown

      method load_smtlib2 str =
        let ast = Z3.SMT.parse_smtlib2_string z3 str [] [] [] [] in
        let sym_of_decl =
          let cos =
            Memo.memo (fun (name, typ) -> mk_symbol context ~name typ)
          in
          fun decl ->
            let open Z3 in
            let sym = FuncDecl.get_name decl in
            assert (FuncDecl.get_domain decl = []);
            cos (Symbol.to_string sym, typ_of_sort (FuncDecl.get_range decl))
        in
        match refine context (of_z3 context sym_of_decl ast) with
        | `Formula phi -> phi
        | `Term _ -> invalid_arg "load_smtlib2"
    end

let mk_z3_solver ?(theory="") ctx =
  if theory = "" then
    (new z3_solver ctx#ark ctx#z3 (Z3.Solver.mk_simple_solver ctx#z3))
  else
    (new z3_solver ctx#ark ctx#z3 (Z3.Solver.mk_solver_s ctx#z3 theory))

let mk_solver ark = mk_z3_solver (mk_context ark [])

let get_model ark phi = (mk_context ark [])#get_model phi

let is_sat ark phi = (mk_context ark [])#is_sat phi

let optimize_box ark phi objectives =
  (mk_context ark [])#optimize_box phi objectives


module CHC = struct
  type 'a solver =
    { ctx : 'a z3_context;
      error : symbol;
      fp : Z3.Fixedpoint.fixedpoint }

  let mk_solver ctx =
    let fp = Z3.Fixedpoint.mk_fixedpoint ctx#z3 in
    let error = mk_symbol ctx#ark ~name:"error" (`TyFun ([], `TyBool)) in
    let error_decl = decl_of_symbol ctx#z3 ctx#ark error in
    let params = Z3.Params.mk_params ctx#z3 in
    let sym x = Z3.Symbol.mk_string ctx#z3 x in
    Z3.Params.add_bool params (sym "xform.slice") false;
    Z3.Params.add_bool params (sym "xform.inline_linear") false;
    Z3.Params.add_bool params (sym "xform.inline_eager") false;
    Z3.Params.add_bool params (sym "pdr.utvpi") false;
    Z3.Fixedpoint.set_parameters fp params;

    Z3.Fixedpoint.register_relation fp error_decl;
    { ctx; error; fp }

  let register_relation solver relation =
    let decl = decl_of_symbol solver.ctx#z3 solver.ctx#ark relation in
    Z3.Fixedpoint.register_relation solver.fp decl

  let add solver phis =
    Z3.Fixedpoint.add solver.fp (List.map solver.ctx#of_formula phis)

  let pop solver = Z3.Fixedpoint.pop solver.fp

  let push solver = Z3.Fixedpoint.push solver.fp

  module M = ArkUtil.Int.Map
  let add_rule solver hypothesis conclusion =
    let ark = solver.ctx#ark in
    let var_table = free_vars (mk_if ark hypothesis conclusion) in
    let rename =
      let table = Hashtbl.create 991 in
      BatHashtbl.enum var_table
      |> BatEnum.iteri (fun i (j, typ) -> Hashtbl.add table j (mk_var ark i typ));
      fun (i, t) -> Hashtbl.find table i
    in
    let rule =
      match destruct ark conclusion with
      | `App (_, _) ->
        let hypothesis =
          solver.ctx#of_formula (substitute ark rename hypothesis)
        in
        let conclusion =
          solver.ctx#of_formula (substitute ark rename conclusion)
        in
        Z3.Boolean.mk_implies solver.ctx#z3 hypothesis conclusion
      | _ ->
        let hypothesis =
          mk_and ark [hypothesis; (mk_not ark conclusion)]
          |> substitute ark rename
          |> solver.ctx#of_formula
        in
        let conclusion =
          mk_app ark solver.error []
          |> solver.ctx#of_formula
        in
        Z3.Boolean.mk_implies solver.ctx#z3 hypothesis conclusion
    in
    let quantified_rule =
      let types =
        BatHashtbl.values var_table
        /@ (sort_of_typ solver.ctx#z3)
        |> BatList.of_enum
      in
      let names =
        List.map (fun _ -> Z3.Symbol.mk_string solver.ctx#z3 "_") types
      in
      Z3.Quantifier.mk_forall
        solver.ctx#z3
        types
        names
        rule
        None
        []
        []
        None
        None
      |> Z3.Quantifier.expr_of_quantifier
    in
    Z3.Fixedpoint.add_rule solver.fp quantified_rule None

  let check solver assumptions =
    let goal = solver.ctx#of_formula (mk_app solver.ctx#ark solver.error []) in
    match Z3.Fixedpoint.query solver.fp goal with
    | Z3.Solver.UNSATISFIABLE -> `Sat
    | Z3.Solver.SATISFIABLE -> `Unsat
    | Z3.Solver.UNKNOWN -> `Unknown

  let get_solution solver relation =
    let ark = solver.ctx#ark in
    let decl = decl_of_symbol solver.ctx#z3 ark relation in
    if Z3.Fixedpoint.get_num_levels solver.fp decl = 0 then
      mk_false ark (* 0 levels -> never appears in the head of a rule *)
    else
      match Z3.Fixedpoint.get_cover_delta solver.fp (-1) decl with
      | Some inv -> solver.ctx#formula_of inv
      | None -> assert false

  let to_string solver = Z3.Fixedpoint.to_string solver.fp
end

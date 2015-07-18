open Syntax

include Apak.Log.Make(struct let name = "ark.smt" end)

module type TranslationContext = sig
  include BuilderContext
  include EvalContext with type term := term and type formula := formula
end

exception Unknown_result

let bool_val x =
  match Z3.Boolean.get_bool_value x with
  | Z3enums.L_TRUE -> true
  | Z3enums.L_FALSE -> false
  | Z3enums.L_UNDEF -> invalid_arg "bool_val: not a Boolean"

let int_val x = Z3.Arithmetic.Integer.get_int x

module MakeZ3 (Opt : sig val opts : (string * string) list end)() = struct
  type term = Z3.Expr.expr
  type formula = Z3.Expr.expr
  open Z3
  let ctx = mk_context Opt.opts
  let int_sort = Arithmetic.Integer.mk_sort ctx
  let real_sort = Arithmetic.Real.mk_sort ctx
  let bool_sort = Boolean.mk_sort ctx

  let sort_of_typ = function
    | TyInt  -> int_sort
    | TyReal -> real_sort

  let typ_of_sort sort =
    let open Z3enums in
    match Sort.get_sort_kind sort with
    | REAL_SORT -> TyReal
    | INT_SORT -> TyInt
    | _ -> invalid_arg "typ_of_sort"    

  module Term = struct
    type t = term
    let rec eval : ('a open_term -> 'a) -> t -> 'a = fun alg ast ->
      let open Z3enums in
      match AST.get_ast_kind (Expr.ast_of_expr ast) with
      | APP_AST -> begin
          let decl = Expr.get_func_decl ast in
          let args = List.map (eval alg) (Expr.get_args ast) in
          match FuncDecl.get_decl_kind decl, args with
          | (OP_UNINTERPRETED, []) ->
            alg (`Const (Symbol.get_int (FuncDecl.get_name decl)))
          | (OP_ADD, args) -> alg (`Add args)
          | (OP_MUL, args) -> alg (`Mul args)
          | (OP_SUB, [x;y]) -> alg (`Add [x; alg (`Unop (`Neg, y))])
          | (OP_UMINUS, [x]) -> alg (`Unop (`Neg, x))
          | (OP_MOD, [x;y]) -> alg (`Binop (`Mod, x, y))
          | (OP_IDIV, [x;y]) -> alg (`Unop (`Floor, alg (`Binop (`Div, x, y))))
          | (OP_DIV, [x;y]) -> alg (`Binop (`Div, x, y))
          | (OP_TO_REAL, [x]) -> x
          | (OP_TO_INT, [x]) -> alg (`Unop (`Floor, x))
          | (_, _) -> invalid_arg "Term.eval: unknown application"
        end
      | NUMERAL_AST ->
        alg (`Real (QQ.of_string (Arithmetic.Real.numeral_to_string ast)))
      | VAR_AST ->
        let index = Quantifier.get_index ast in
        alg (`Var (index, (typ_of_sort (Expr.get_sort ast))))
      | QUANTIFIER_AST
      | FUNC_DECL_AST
      | SORT_AST
      | UNKNOWN_AST -> invalid_arg "Term.eval: unknown ast type"

  end
  module Formula = struct
    type t = formula
    let rec eval alg ast =
      let open Z3enums in
      match AST.get_ast_kind (Expr.ast_of_expr ast) with
      | APP_AST -> begin
          let decl = Expr.get_func_decl ast in
          match FuncDecl.get_decl_kind decl, Expr.get_args ast with
          | (OP_TRUE, []) -> alg `Tru
          | (OP_FALSE, []) -> alg `Fls
          | (OP_AND, args) -> alg (`And (List.map (eval alg) args))
          | (OP_OR, args) -> alg (`Or (List.map (eval alg) args))
          | (OP_IFF, [phi;psi]) ->
            let phi, psi = eval alg phi, eval alg psi in
            alg (`Or [alg (`And [phi; psi]);
                      alg (`Not (alg (`Or [phi; psi])))])
          | (OP_NOT, [phi]) -> alg (`Not (eval alg phi))
          | (OP_EQ, [s; t]) -> alg (`Atom (`Eq, s, t))
          | (OP_LE, [s; t]) -> alg (`Atom (`Leq, s, t))
          | (OP_GE, [s; t]) -> alg (`Atom (`Leq, t, s))
          | (OP_LT, [s; t]) -> alg (`Atom (`Lt, s, t))
          | (OP_GT, [s; t]) -> alg (`Atom (`Lt, t, s))
          | _ ->
            Apak.Log.invalid_argf "Formula.eval: %s" (Z3.Expr.to_string ast)
        end
      | QUANTIFIER_AST ->
        let ast = Quantifier.quantifier_of_expr ast in
        let qt =
          if Quantifier.is_existential ast then `Exists
          else `Forall
        in
        List.fold_left2
          (fun body name sort ->
             alg (`Quantify (qt,
                             Z3.Symbol.to_string name,
                             typ_of_sort sort,
                             body)))
          (eval alg (Quantifier.get_body ast))
          (Quantifier.get_bound_variable_names ast)
          (Quantifier.get_bound_variable_sorts ast)            
      | NUMERAL_AST
      | VAR_AST
      | FUNC_DECL_AST
      | SORT_AST
      | UNKNOWN_AST -> invalid_arg "Formula.eval"
  end
  
  let mk_add = Arithmetic.mk_add ctx
  let mk_mul = Arithmetic.mk_mul ctx
  let mk_div = Arithmetic.mk_div ctx
  let mk_mod = Arithmetic.Integer.mk_mod ctx
  let mk_var i typ = Quantifier.mk_bound ctx i (sort_of_typ typ)
  let mk_real qq =
    match QQ.to_zz qq with
    | Some zz -> Arithmetic.Integer.mk_numeral_s ctx (ZZ.show zz)
    | None -> Arithmetic.Real.mk_numeral_s ctx (QQ.show qq)
  let mk_const k =
    Arithmetic.Integer.mk_const ctx (Symbol.mk_int ctx k) (* TODO !!!! *)
  let mk_floor = Arithmetic.Real.mk_real2int ctx
  let mk_neg = Arithmetic.mk_unary_minus ctx

  let mk_true = Boolean.mk_true ctx
  let mk_false = Boolean.mk_false ctx
  let mk_and = Boolean.mk_and ctx
  let mk_or = Boolean.mk_or ctx
  let mk_not = Boolean.mk_not ctx
  let mk_quantified qt ?name:(name="_") typ phi =
    let mk = match qt with
      | `Exists -> Quantifier.mk_exists
      | `Forall -> Quantifier.mk_forall
    in
    mk
      ctx
      [sort_of_typ typ]
      [Symbol.mk_string ctx name]
      phi
      None
      []
      []
      None
      None
    |> Z3.Quantifier.expr_of_quantifier
  let mk_exists = mk_quantified `Exists
  let mk_forall = mk_quantified `Forall
  let mk_lt = Arithmetic.mk_lt ctx
  let mk_leq = Arithmetic.mk_le ctx
  let mk_eq = Boolean.mk_eq ctx
end

module MakeSolver
    (C : TranslationContext)
    (Opt : sig val opts : (string * string) list end)
    () = struct

  module Z3C = MakeZ3(Opt)()
  module Z3Of = MakeTranslator(C)(Z3C)
  module OfZ3 = MakeTranslator(Z3C)(C)

  type solver = Z3.Solver.solver
  type model = Z3.Model.model

  let ctx = Z3C.ctx

  let term_of = OfZ3.term
  let formula_of = OfZ3.formula
  let of_term = Z3Of.term
  let of_formula = Z3Of.formula

  module Solver = struct
    let mk_solver () = Z3.Solver.mk_simple_solver Z3C.ctx
    let add s formulae = Z3.Solver.add s (List.map Z3Of.formula formulae)

    let push = Z3.Solver.push
    let pop = Z3.Solver.pop

    let check s args =
      match Z3.Solver.check s (List.map Z3Of.formula args) with
      | Z3.Solver.SATISFIABLE -> `Sat
      | Z3.Solver.UNSATISFIABLE -> `Unsat
      | Z3.Solver.UNKNOWN -> `Unknown

    let get_model : solver -> [`Sat of model | `Unknown | `Unsat ] = fun s ->
      match check s [] with
      | `Sat ->
        begin match Z3.Solver.get_model s with
          | Some m -> `Sat m
          | None -> `Unknown
        end
      | `Unsat -> `Unsat
      | `Unknown -> `Unknown
  end

  module Model = struct
    let eval_int m term =
      match Z3.Model.eval m (Z3Of.term term) true with
      | Some x -> ZZ.of_string (Z3.Arithmetic.Integer.numeral_to_string x)
      | None -> invalid_arg "eval_int: not an integer term"

    let eval_real m term =
      match Z3.Model.eval m (Z3Of.term term) true with
      | Some x -> QQ.of_string (Z3.Arithmetic.Real.numeral_to_string x)
      | None -> invalid_arg "eval_real: not a real term"

    let sat m phi =
      match Z3.Model.eval m (Z3Of.formula phi) true with
      | Some x -> bool_val x
      | None -> assert false

    let to_string = Z3.Model.to_string
  end

  let interpolate_seq seq =
    let rec make_pattern phi = function
      | [psi] ->
        Z3C.mk_and [
          Z3.Interpolation.mk_interpolant Z3C.ctx phi;
          Z3Of.formula psi
        ]
      | psi::rest ->
        make_pattern
          (Z3C.mk_and
             [Z3.Interpolation.mk_interpolant ctx phi;
              Z3Of.formula psi])
          rest
      | [] ->
        invalid_arg "interpolate_seq: input sequence must be of length >= 2"
    in
    let params = Z3.Params.mk_params ctx in
    let pattern =
      if seq = [] then
        invalid_arg "interpolate_seq: input sequence must be of length >= 2";
      make_pattern (Z3Of.formula (List.hd seq)) (List.tl seq)
    in
    match Z3.Interpolation.compute_interpolant ctx pattern params with
    | (_, Some interp, None) -> `Unsat (List.map OfZ3.formula interp)
    | (_, None, Some m) -> `Sat m
    | (_, _, _) -> `Unknown

  let is_sat phi =
    let s = Solver.mk_solver () in
    Solver.add s [phi];
    Solver.check s []

  let get_model phi =
    let s = Solver.mk_solver () in
    Solver.add s [phi];
    Solver.get_model s

  let implies phi psi =
    let s = Solver.mk_solver () in
    Z3.Solver.add s [
      Z3Of.formula phi;
      Z3C.mk_not (Z3Of.formula psi)
    ];
    match Solver.check s [] with
    | `Sat -> false
    | `Unsat -> true
    | `Unknown -> raise Unknown_result
end

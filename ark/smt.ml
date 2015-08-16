open Syntax
open BatPervasives

include Apak.Log.Make(struct let name = "ark.smt" end)

module type TranslationContext = sig
  include BuilderContext
  include EvalContext with type term := term and type formula := formula
  val const_typ : const_sym -> typ
end

exception Unknown_result

let bool_val x =
  match Z3.Boolean.get_bool_value x with
  | Z3enums.L_TRUE -> true
  | Z3enums.L_FALSE -> false
  | Z3enums.L_UNDEF -> invalid_arg "bool_val: not a Boolean"

let int_val x = Z3.Arithmetic.Integer.get_int x

let typ_of_sort sort =
  let open Z3enums in
  match Z3.Sort.get_sort_kind sort with
  | REAL_SORT -> TyReal
  | INT_SORT -> TyInt
  | _ -> invalid_arg "typ_of_sort"


module Make
    (Opt : sig val opts : (string * string) list end)
    () = struct

  type expr = Z3.Expr.expr
  type func_decl = Z3.FuncDecl.func_decl
  type solver = Z3.Solver.solver
  type model = Z3.Model.model

  type 'a open_expr = [
    | `Real of QQ.t
    | `App of func_decl * 'a list
    | `Var of int * typ
    | `Add of 'a list
    | `Mul of 'a list
    | `Binop of [ `Div | `Mod ] * 'a * 'a
    | `Unop of [ `Floor | `Neg ] * 'a
    | `Tru
    | `Fls
    | `And of 'a list
    | `Or of 'a list
    | `Not of 'a
    | `Quantify of [`Exists | `Forall] * string * typ * 'a
    | `Atom of [`Eq | `Leq | `Lt] * 'a * 'a
  ]

  open Z3

  let ctx = mk_context Opt.opts
  let int_sort = Arithmetic.Integer.mk_sort ctx
  let real_sort = Arithmetic.Real.mk_sort ctx
  let bool_sort = Boolean.mk_sort ctx

  let sort_of_typ = function
    | TyInt  -> int_sort
    | TyReal -> real_sort

  let rec eval alg ast =
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
        | (OP_IFF, [phi;psi]) ->
          alg (`Or [alg (`And [phi; psi]);
                    alg (`Not (alg (`Or [phi; psi])))])
        | (OP_NOT, [phi]) -> alg (`Not phi)
        | (OP_EQ, [s; t]) -> alg (`Atom (`Eq, s, t))
        | (OP_LE, [s; t]) -> alg (`Atom (`Leq, s, t))
        | (OP_GE, [s; t]) -> alg (`Atom (`Leq, t, s))
        | (OP_LT, [s; t]) -> alg (`Atom (`Lt, s, t))
        | (OP_GT, [s; t]) -> alg (`Atom (`Lt, t, s))
        | (_, _) -> invalid_arg "eval: unknown application"
      end
    | NUMERAL_AST ->
      alg (`Real (QQ.of_string (Arithmetic.Real.numeral_to_string ast)))
    | VAR_AST ->
      let index = Quantifier.get_index ast in
      alg (`Var (index, (typ_of_sort (Expr.get_sort ast))))
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
    | FUNC_DECL_AST
    | SORT_AST
    | UNKNOWN_AST -> invalid_arg "eval: unknown ast type"

  let mk_sub x y = Arithmetic.mk_sub ctx [x; y]
  let mk_add = Arithmetic.mk_add ctx
  let mk_mul = Arithmetic.mk_mul ctx
  let mk_div = Arithmetic.mk_div ctx
  let mk_mod = Arithmetic.Integer.mk_mod ctx
  let mk_var i typ = Quantifier.mk_bound ctx i (sort_of_typ typ)
  let mk_real qq =
    match QQ.to_zz qq with
    | Some zz -> Arithmetic.Integer.mk_numeral_s ctx (ZZ.show zz)
    | None -> Arithmetic.Real.mk_numeral_s ctx (QQ.show qq)
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
  let mk_app = Expr.mk_app ctx
  let mk_const k = mk_app k []
  let mk = function
    | `Real qq -> mk_real qq
    | `App (func, args) -> mk_app func args
    | `Var (i, typ) -> mk_var i typ
    | `Add sum -> mk_add sum
    | `Mul product -> mk_mul product
    | `Binop (`Div, x, y) -> mk_div x y
    | `Binop (`Mod, x, y) -> mk_mod x y
    | `Unop (`Floor, x) -> mk_floor x
    | `Unop (`Neg, x) -> mk_neg x
    | `Tru -> mk_true
    | `Fls -> mk_false
    | `And conjuncts -> mk_and conjuncts
    | `Or disjuncts -> mk_or disjuncts
    | `Not phi -> mk_not phi
    | `Quantify (qt, name, typ, phi) -> mk_quantified qt ~name:name typ phi
    | `Atom (`Eq, x, y) -> mk_eq x y
    | `Atom (`Lt, x, y) -> mk_lt x y
    | `Atom (`Leq, x, y) -> mk_leq x y

  module Solver = struct
    let mk_solver () = Z3.Solver.mk_simple_solver ctx
    let add = Z3.Solver.add
    let push = Z3.Solver.push
    let pop = Z3.Solver.pop

    let check s args =
      match Z3.Solver.check s args with
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
      match Z3.Model.eval m term true with
      | Some x -> ZZ.of_string (Z3.Arithmetic.Integer.numeral_to_string x)
      | None -> invalid_arg "eval_int: not an integer term"

    let eval_real m term =
      match Z3.Model.eval m term true with
      | Some x -> QQ.of_string (Z3.Arithmetic.Real.numeral_to_string x)
      | None -> invalid_arg "eval_real: not a real term"

    let sat m phi =
      match Z3.Model.eval m phi true with
      | Some x -> bool_val x
      | None -> assert false

    let to_string = Z3.Model.to_string
  end

end

module MakeSolver
    (C : TranslationContext)
    (Opt : sig val opts : (string * string) list end)
    () = struct

  module Z3C = Make(Opt)()

  let of_term term =
    let alg = function
      | `Real qq -> Z3C.mk_real qq
      | `Const sym ->
        let id = Z3.Symbol.mk_int Z3C.ctx (Obj.magic sym) in
        let sort = match C.const_typ sym with
          | TyInt -> Z3C.int_sort
          | TyReal -> Z3C.real_sort
        in
        let decl = Z3.FuncDecl.mk_const_decl Z3C.ctx id sort in
        Z3C.mk_const decl
      | `Var (i, typ) -> Z3C.mk_var i typ
      | `Add sum -> Z3C.mk_add sum
      | `Mul product -> Z3C.mk_mul product
      | `Binop (`Div, s, t) -> Z3C.mk_div s t
      | `Binop (`Mod, s, t) -> Z3C.mk_mod s t
      | `Unop (`Floor, t) -> Z3C.mk_floor t
      | `Unop (`Neg, t) -> Z3C.mk_neg t
    in
    C.Term.eval alg term

  let of_formula phi =
    let alg = function
      | `Tru -> Z3C.mk_and []
      | `Fls -> Z3C.mk_or []
      | `And conjuncts -> Z3C.mk_and conjuncts
      | `Or disjuncts -> Z3C.mk_or disjuncts
      | `Not phi -> Z3C.mk_not phi
      | `Quantify (`Exists, name, typ, phi) ->
        Z3C.mk_exists ~name:name typ phi
      | `Quantify (`Forall, name, typ, phi) ->
        Z3C.mk_forall ~name:name typ phi
      | `Atom (`Eq, s, t) -> Z3C.mk_eq (of_term s) (of_term t)
      | `Atom (`Leq, s, t) -> Z3C.mk_leq (of_term s) (of_term t)
      | `Atom (`Lt, s, t) -> Z3C.mk_lt (of_term s) (of_term t)
    in
    C.Formula.eval alg phi

  let of_z3 expr =
    let term = function
      | `Term t -> t
      | _ -> invalid_arg "of_z3.term"
    in
    let formula = function
      | `Formula phi -> phi
      | _ -> invalid_arg "of_z3.formula"
    in
    let alg = function
      | `Real qq -> `Term (C.mk_real qq)
      | `Var (i, typ) -> `Term (C.mk_var i typ)
      | `App (decl, []) ->
        let id = Z3.Symbol.get_int (Z3.FuncDecl.get_name decl) in
        `Term (C.mk_const (Obj.magic id))
      | `Add sum -> `Term (C.mk_add (List.map term sum))
      | `Mul product -> `Term (C.mk_mul (List.map term product))
      | `Binop (op, s, t) ->
        let mk_op = match op with
          | `Div -> C.mk_div
          | `Mod -> C.mk_mod
        in
        `Term (mk_op (term s) (term t))
      | `Unop (`Floor, t) -> `Term (C.mk_floor (term t))
      | `Unop (`Neg, t) -> `Term (C.mk_neg (term t))
      | `Tru -> `Formula (C.mk_and [])
      | `Fls -> `Formula (C.mk_or [])
      | `And conjuncts -> `Formula (C.mk_and (List.map formula conjuncts))
      | `Or disjuncts -> `Formula (C.mk_or (List.map formula disjuncts))
      | `Not phi -> `Formula (C.mk_not (formula phi))
      | `Quantify (`Exists, name, typ, phi) ->
        `Formula (C.mk_exists ~name:name typ (formula phi))
      | `Quantify (`Forall, name, typ, phi) ->
        `Formula (C.mk_forall ~name:name typ (formula phi))
      | `Atom (`Eq, s, t) -> `Formula (C.mk_eq (term s) (term t))
      | `Atom (`Leq, s, t) -> `Formula (C.mk_leq (term s) (term t))
      | `Atom (`Lt, s, t) -> `Formula (C.mk_lt (term s) (term t))
      | `App (_, _) -> invalid_arg "term_of"
    in
    Z3C.eval alg expr

  let term_of term =
    match of_z3 term with
    | `Term t -> t
    | `Formula _ -> invalid_arg "term_of"

  let formula_of phi =
    match of_z3 phi with
    | `Formula phi -> phi
    | `Term _ -> invalid_arg "formula_of"

  type solver = Z3.Solver.solver
  type model = Z3.Model.model
  type fixedpoint = Z3.Fixedpoint.fixedpoint

  let ctx = Z3C.ctx

  module Solver = struct
    let mk_solver () = Z3.Solver.mk_simple_solver Z3C.ctx
    let add s formulae = Z3.Solver.add s (List.map of_formula formulae)

    let push = Z3.Solver.push
    let pop = Z3.Solver.pop

    let check s args =
      match Z3.Solver.check s (List.map of_formula args) with
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
      match Z3.Model.eval m (of_term term) true with
      | Some x -> ZZ.of_string (Z3.Arithmetic.Integer.numeral_to_string x)
      | None -> invalid_arg "eval_int: not an integer term"

    let eval_real m term =
      match Z3.Model.eval m (of_term term) true with
      | Some x -> QQ.of_string (Z3.Arithmetic.Real.numeral_to_string x)
      | None -> invalid_arg "eval_real: not a real term"

    let sat m phi =
      match Z3.Model.eval m (of_formula phi) true with
      | Some x -> bool_val x
      | None -> assert false

    let to_string = Z3.Model.to_string
  end

  let interpolate_seq seq =
    let rec make_pattern phi = function
      | [psi] ->
        Z3C.mk_and [
          Z3.Interpolation.mk_interpolant Z3C.ctx phi;
          of_formula psi
        ]
      | psi::rest ->
        make_pattern
          (Z3C.mk_and
             [Z3.Interpolation.mk_interpolant ctx phi;
              of_formula psi])
          rest
      | [] ->
        invalid_arg "interpolate_seq: input sequence must be of length >= 2"
    in
    let params = Z3.Params.mk_params ctx in
    let pattern =
      if seq = [] then
        invalid_arg "interpolate_seq: input sequence must be of length >= 2";
      make_pattern (of_formula (List.hd seq)) (List.tl seq)
    in
    match Z3.Interpolation.compute_interpolant ctx pattern params with
    | (_, Some interp, None) -> `Unsat (List.map formula_of interp)
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
      of_formula phi;
      Z3C.mk_not (of_formula psi)
    ];
    match Solver.check s [] with
    | `Sat -> false
    | `Unsat -> true
    | `Unknown -> raise Unknown_result

  let equiv phi psi =
    let s = Solver.mk_solver () in
    Z3.Solver.add s [Z3C.mk_or [
        Z3C.mk_and [of_formula phi; Z3C.mk_not (of_formula psi)];
        Z3C.mk_and [of_formula psi; Z3C.mk_not (of_formula phi)];
      ]];
    match Solver.check s [] with
    | `Sat -> false
    | `Unsat -> true
    | `Unknown -> raise Unknown_result
end

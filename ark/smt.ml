open Syntax
open BatPervasives

include Apak.Log.Make(struct let name = "ark.smt" end)

module type TranslationContext = sig
  include BuilderContext
  include EvalContext with type term := term and type formula := formula
  val const_typ : const_sym -> typ
  val mk_skolem : ?name:string -> typ -> const_sym
end

exception Unknown_result

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
    | `Var of int * typ_arith
    | `Add of 'a list
    | `Mul of 'a list
    | `Binop of [ `Div | `Mod ] * 'a * 'a
    | `Unop of [ `Floor | `Neg ] * 'a
    | `Tru
    | `Fls
    | `And of 'a list
    | `Or of 'a list
    | `Not of 'a
    | `Quantify of [`Exists | `Forall] * string * typ_arith * 'a
    | `Atom of [`Eq | `Leq | `Lt] * 'a * 'a
  ]

  open Z3

  let ctx = mk_context Opt.opts
  let int_sort = Arithmetic.Integer.mk_sort ctx
  let real_sort = Arithmetic.Real.mk_sort ctx
  let bool_sort = Boolean.mk_sort ctx

  let sort_of_typ = function
    | `TyInt  -> int_sort
    | `TyReal -> real_sort
    | `TyBool -> bool_sort

  let mk_fresh_decl ?(name="f") params result =
    Z3.FuncDecl.mk_fresh_func_decl
      ctx
      name
      (List.map sort_of_typ params)
      (sort_of_typ result)

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
        | (_, _) -> invalid_arg ("eval: unknown application: "
                                 ^ (Expr.to_string ast))
      end
    | NUMERAL_AST ->
      alg (`Real (qq_val ast))
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
    let reset = Z3.Solver.reset

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
      | Some x -> zz_val x
      | None -> invalid_arg "eval_int: not an integer term"

    let eval_real m term =
      match Z3.Model.eval m term true with
      | Some x -> qq_val x
      | None -> invalid_arg "eval_real: not a real term"

    let eval_func m decl =
      let open Model.FuncInterp in
      match Model.get_func_interp m decl with
      | Some interp ->
        let entries =
          List.map (fun entry ->
              (FuncEntry.get_args entry, FuncEntry.get_value entry)
            ) (get_entries interp)
        in
        (entries, get_else interp)
      | None -> invalid_arg "eval_func: No interpretation for function decl"

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
          | `TyInt -> Z3C.int_sort
          | `TyReal -> Z3C.real_sort
          | `TyBool -> Z3C.bool_sort
          | `TyFun (_,_) -> invalid_arg "z3_of.term"
        in
        let decl = Z3.FuncDecl.mk_const_decl Z3C.ctx id sort in
        Z3C.mk_const decl
      | `Var (i, `TyFun (_, _))
      | `Var (i, `TyBool) -> invalid_arg "z3_of.term"
      | `Var (i, `TyInt) -> Z3C.mk_var i `TyInt
      | `Var (i, `TyReal) -> Z3C.mk_var i `TyReal
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

  let of_z3 const_of_decl expr =
    let term = function
      | `Term t -> t
      | `Formula phi ->
        invalid_arg ("of_z3.term:" ^ (Z3.Expr.to_string (of_formula phi)))
    in
    let formula = function
      | `Formula phi -> phi
      | _ -> invalid_arg "of_z3.formula"
    in
    let alg = function
      | `Real qq -> `Term (C.mk_real qq)
      | `Var (i, `TyInt) -> `Term (C.mk_var i `TyInt)
      | `Var (i, `TyReal) -> `Term (C.mk_var i `TyReal)
      | `App (decl, []) ->
        let const_sym = const_of_decl decl in
        begin match C.const_typ const_sym with
          | `TyBool ->
            `Formula (C.mk_eq (C.mk_real QQ.zero) (C.mk_const const_sym))
          | `TyInt | `TyReal -> `Term (C.mk_const const_sym)
          | `TyFun (_, _) -> assert false (* Shouldn't appear with zero args *)
        end
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
      | `Atom (`Eq, `Term s, `Term t) -> `Formula (C.mk_eq s t)
      | `Atom (`Eq, `Formula phi, `Formula psi) ->
        `Formula (C.mk_or [C.mk_not phi; psi])
      | `Atom (`Leq, s, t) -> `Formula (C.mk_leq (term s) (term t))
      | `Atom (`Lt, s, t) -> `Formula (C.mk_lt (term s) (term t))
      | `Atom (`Eq, _, _) -> invalid_arg "of_z3"
      | `App (decl, args) ->
        invalid_arg ("of_z3: " ^ (Z3.FuncDecl.to_string decl))
    in
    Z3C.eval alg expr

  (* const_of_decl is sufficient for round-tripping, since const_sym's become
     int symbols *)
  let const_of_decl decl =
    let sym = Z3.FuncDecl.get_name decl in
    assert (Z3.Symbol.is_int_symbol sym);
    Obj.magic (Z3.Symbol.get_int sym)

  let term_of term =
    match of_z3 const_of_decl term with
    | `Term t -> t
    | `Formula _ -> invalid_arg "term_of"

  let formula_of phi =
    match of_z3 const_of_decl phi with
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
    let reset = Z3.Solver.reset

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

    let get_unsat_core solver assumptions =
      match check solver assumptions with
      | `Sat -> `Sat
      | `Unknown -> `Unknown
      | `Unsat ->
        `Unsat (List.map formula_of (Z3.Solver.get_unsat_core solver))
  end

  module Model = struct
    let eval_int m term =
      match Z3.Model.eval m (of_term term) true with
      | Some x -> zz_val x
      | None -> invalid_arg "eval_int: not an integer term"

    let eval_real m term =
      match Z3.Model.eval m (of_term term) true with
      | Some x -> qq_val x
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

  let of_goal g =
    let open Z3 in
    List.map formula_of (Goal.get_formulas g)
    |> C.mk_and

  let of_apply_result result =
    let open Z3 in
    List.map of_goal (Tactic.ApplyResult.get_subgoals result)
    |> C.mk_and

  let qe phi =
    let open Z3 in
    let solve = Tactic.mk_tactic ctx "qe" in
    let simpl = Tactic.mk_tactic ctx "simplify" in
    let qe = Tactic.and_then ctx solve simpl [] in
    let g = Goal.mk_goal ctx false false false in
    Goal.add g [of_formula phi];
    of_apply_result (Tactic.apply qe g None)

  let qe_sat phi =
    let open Z3 in
    let solve = Tactic.mk_tactic ctx "qe-sat" in
    let simpl = Tactic.mk_tactic ctx "simplify" in
    let qe = Tactic.and_then ctx solve simpl [] in
    let g = Goal.mk_goal ctx false false false in
    Goal.add g [of_formula phi];
    is_sat (of_apply_result (Tactic.apply qe g None))

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

  let optimize_box phi terms =
    let open Z3.Optimize in
    let opt = mk_opt ctx in
    let params = Z3.Params.mk_params ctx in
    let sym = Z3.Symbol.mk_string ctx in
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
	  Apak.Log.fatalf "Smt.optimize_box: %s" (Z3.Expr.to_string lo)
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
	  Apak.Log.fatalf "Smt.optimize_box: %s" (Z3.Expr.to_string hi)
      in
      Interval.make lower upper
    in
    match check opt with
    | Z3.Solver.SATISFIABLE -> `Sat (List.map mk_interval handles)
    | Z3.Solver.UNSATISFIABLE -> `Unsat
    | Z3.Solver.UNKNOWN -> `Unknown

  let load_smtlib2 str =
    let ast = Z3.SMT.parse_smtlib2_string ctx str [] [] [] [] in
    let const_of_decl =
      let cos = Apak.Memo.memo (fun (name, typ) -> C.mk_skolem ~name typ) in
      fun decl ->
        let open Z3 in
        let sym = FuncDecl.get_name decl in
        assert (FuncDecl.get_domain decl = []);
        assert (Symbol.is_string_symbol sym);
        cos (Symbol.get_string sym, typ_of_sort (FuncDecl.get_range decl))
    in
    match of_z3 const_of_decl ast with
    | `Formula phi -> phi
    | `Term _ -> invalid_arg "load_smtlib2"
end

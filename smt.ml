open Syntax

module T = Term
module F = Formula

include Apak.Log.Make(struct let name = "ark.smt" end)

exception Unknown_result

let bool_val x =
  match Z3.Boolean.get_bool_value x with
  | Z3enums.L_TRUE -> true
  | Z3enums.L_FALSE -> false
  | Z3enums.L_UNDEF -> invalid_arg "bool_val: not a Boolean"

let int_val x = Z3.Arithmetic.Integer.get_int x

class ['a] context opts = object(self)
  val z3 = Z3.mk_context opts
  method z3 = z3
  method int_sort = Z3.Arithmetic.Integer.mk_sort z3
  method real_sort = Z3.Arithmetic.Real.mk_sort z3
  method bool_sort = Z3.Boolean.mk_sort z3

  method sort_of_typ = function
    | TyInt -> self#int_sort
    | TyReal -> self#real_sort

  method typ_of_sort sort =
    let open Z3enums in
    match Z3.Sort.get_sort_kind sort with
    | REAL_SORT -> TyReal
    | INT_SORT -> TyInt
    | _ -> invalid_arg "typ_of_sort"


  method of_term =
    let alg = function
      | `Real qq ->
        (match QQ.to_zz qq with
         | Some zz -> Z3.Arithmetic.Integer.mk_numeral_s z3 (ZZ.show zz)
         | None -> Z3.Arithmetic.Real.mk_numeral_s z3 (QQ.show qq))
      | `Binop (`Add, s, t) -> Z3.Arithmetic.mk_add z3 [s; t]
      | `Binop (`Mul, s, t) -> Z3.Arithmetic.mk_mul z3 [s; t]
      | `Binop (`Div, s, t) -> Z3.Arithmetic.mk_div z3 s t
      | `Binop (`Mod, s, t) -> Z3.Arithmetic.Integer.mk_mod z3 s t
      | `Var (i, typ) -> Z3.Quantifier.mk_bound z3 i (self#sort_of_typ typ)
      | `Const k ->
        Z3.Symbol.mk_int z3 (Syntax.id_of_symbol k)
        |> Z3.Arithmetic.Integer.mk_const z3
      | `Unop (`Floor, t) -> Z3.Arithmetic.Real.mk_real2int z3 t
      | `Unop (`Neg, t) -> Z3.Arithmetic.mk_unary_minus z3 t
    in
    T.eval alg

  method of_formula =
    let alg = function
      | `Tru -> Z3.Boolean.mk_true z3
      | `Fls -> Z3.Boolean.mk_false z3
      | `Binop (`And, phi, psi) -> Z3.Boolean.mk_and z3 [phi; psi]
      | `Binop (`Or, phi, psi) -> Z3.Boolean.mk_or z3 [phi; psi]
      | `Not phi -> Z3.Boolean.mk_not z3 phi
      | `Atom (op, s, t) ->
        let mk = match op with
          | `Eq -> Z3.Boolean.mk_eq
          | `Leq -> Z3.Arithmetic.mk_le
          | `Lt -> Z3.Arithmetic.mk_lt
        in
        mk z3 (self#of_term s) (self#of_term t)
      | `Quantify (qt, name, typ, phi) ->
        let mk_quantified = match qt with
          | `Exists -> Z3.Quantifier.mk_exists
          | `Forall -> Z3.Quantifier.mk_forall
        in
        mk_quantified
          z3
          [self#sort_of_typ typ]
          [Z3.Symbol.mk_string z3 name]
          phi
          None
          []
          []
          None
          None
        |> Z3.Quantifier.expr_of_quantifier
    in
    F.eval alg

  method term_of (ctx : 'a Syntax.context) ?env:(env=Env.empty) ast =
    let open Z3 in
    let open Z3enums in
    let rec of_smt ast =
      match AST.get_ast_kind (Expr.ast_of_expr ast) with
      | APP_AST -> begin
          let decl = Expr.get_func_decl ast in
          let args = List.map of_smt (Expr.get_args ast) in
          match FuncDecl.get_decl_kind decl, args with
          | (OP_UNINTERPRETED, []) ->
            symbol_of_id (Symbol.get_int (FuncDecl.get_name decl))
            |> T.mk_const ctx
          | (OP_ADD, args) -> T.mk_sum ctx (BatList.enum args)
          | (OP_MUL, args) -> T.mk_product ctx (BatList.enum args)
          | (OP_SUB, [x;y]) -> T.mk_sub ctx x y
          | (OP_UMINUS, [x]) -> T.mk_neg ctx x
          | (OP_MOD, [x;y]) -> T.mk_mod ctx x y
          | (OP_IDIV, [x;y]) -> T.mk_idiv ctx x y
          | (OP_DIV, [x;y]) -> T.mk_div ctx x y
          | (OP_TO_REAL, [x]) -> x
          | (OP_TO_INT, [x]) -> T.mk_floor ctx x
          | (_, _) -> invalid_arg "term_of: unknown application"
        end
      | NUMERAL_AST ->
        T.mk_real ctx (QQ.of_string (Arithmetic.Real.numeral_to_string ast))
      | VAR_AST ->
        let index = Quantifier.get_index ast in
        T.mk_var ctx index (Env.find env index)
      | QUANTIFIER_AST
      | FUNC_DECL_AST
      | SORT_AST
      | UNKNOWN_AST -> invalid_arg "term_of: unknown ast type"
    in
    of_smt ast

  method formula_of (ctx : 'a Syntax.context) ?env:(env=Env.empty) ast =
    let open Z3 in
    let open Z3enums in
    let smt_term env = self#term_of ctx ~env:env in
    let rec of_smt env ast =
      match AST.get_ast_kind (Expr.ast_of_expr ast) with
      | APP_AST -> begin
          let decl = Expr.get_func_decl ast in
          let args = BatList.enum (Expr.get_args ast) in
          match FuncDecl.get_decl_kind decl with
          | OP_TRUE -> F.mk_true ctx
          | OP_FALSE -> F.mk_false ctx
          | OP_AND ->
            BatEnum.map (of_smt env) args
            |> F.mk_conjunction ctx
          | OP_OR ->
            BatEnum.map (of_smt env) args
            |> F.mk_disjunction ctx
          | OP_IFF -> begin
              match BatList.of_enum (BatEnum.map (of_smt env) args) with
              | [phi;psi] -> F.mk_iff ctx phi psi
              | _ -> assert false
            end
          | OP_NOT -> begin
              match BatList.of_enum (BatEnum.map (of_smt env) args) with
              | [phi] -> F.mk_not ctx phi
              | _ -> assert false
            end
          | OP_EQ -> begin
              match BatList.of_enum (BatEnum.map (smt_term env) args) with
              | [x;y] -> F.mk_eq ctx x y
              | _ -> assert false
            end
          | OP_LE -> begin
              match BatList.of_enum (BatEnum.map (smt_term env) args) with
              | [x;y] -> F.mk_leq ctx x y
              | _ -> assert false
            end
          | OP_GE -> begin
              match BatList.of_enum (BatEnum.map (smt_term env) args) with
              | [x;y] -> F.mk_leq ctx y x
              | _ -> assert false
            end
          | OP_LT -> begin
              match BatList.of_enum (BatEnum.map (smt_term env) args) with
              | [x;y] -> F.mk_lt ctx x y
              | _ -> assert false
            end
          | OP_GT -> begin
              match BatList.of_enum (BatEnum.map (smt_term env) args) with
              | [x;y] -> F.mk_lt ctx y x
              | _ -> assert false
            end
          | _ ->
            Apak.Log.invalid_argf "Smt.formula_of: %s" (Z3.Expr.to_string ast)
        end
      | QUANTIFIER_AST ->
        let ast = Quantifier.quantifier_of_expr ast in
        let env =
          List.fold_left
            (fun env sort -> Env.push (self#typ_of_sort sort) env)
            env
            (Quantifier.get_bound_variable_sorts ast)
        in
        let quantify =
          if Quantifier.is_existential ast then F.mk_exists
          else F.mk_forall
        in
        List.fold_left2
          (fun body name sort ->
             quantify ctx
               ~name:(Z3.Symbol.to_string name)
               (self#typ_of_sort sort)
               body)
          (of_smt env (Quantifier.get_body ast))
          (Quantifier.get_bound_variable_names ast)
          (Quantifier.get_bound_variable_sorts ast)            
      | NUMERAL_AST
      | VAR_AST
      | FUNC_DECL_AST
      | SORT_AST
      | UNKNOWN_AST -> invalid_arg "formula_of"
    in
    of_smt env ast

  method interpolate_seq ctx seq =
    let rec make_pattern phi = function
      | [psi] ->
        Z3.Boolean.mk_and z3 [
          Z3.Interpolation.mk_interpolant z3 phi;
          self#of_formula psi
        ]
      | psi::rest ->
        make_pattern
          (Z3.Boolean.mk_and z3
             [Z3.Interpolation.mk_interpolant z3 phi;
              self#of_formula psi])
          rest
      | [] ->
        invalid_arg "interpolate_seq: input sequence must be of length >= 2"
    in
    let params = Z3.Params.mk_params z3 in
    let pattern =
      if seq = [] then
        invalid_arg "interpolate_seq: input sequence must be of length >= 2";
      make_pattern (self#of_formula (List.hd seq)) (List.tl seq)
    in
    match Z3.Interpolation.compute_interpolant z3 pattern params with
    | (_, Some interp, None) -> Some (List.map (self#formula_of ctx) interp)
    | (_, None, Some _) -> None
    | (_, _, _) -> failwith "interpolate_seq: unknown result"
end

class ['a] model (ctx : 'a context) m = object(self)
  method eval_int term =
    match Z3.Model.eval m (ctx#of_term term) true with
    | Some x -> ZZ.of_string (Z3.Arithmetic.Integer.numeral_to_string x)
    | None -> invalid_arg "eval_int: not an integer term"

  method eval_real term =
    match Z3.Model.eval m (ctx#of_term term) true with
    | Some x -> ZZ.of_string (Z3.Arithmetic.Real.numeral_to_string x)
    | None -> invalid_arg "eval_real: not a real term"

  method sat phi =
    match Z3.Model.eval m (ctx#of_formula phi) true with
    | Some x -> bool_val x
    | None -> assert false

  method to_string () =
    Z3.Model.to_string m
end

class ['a] solver (ctx : 'a context) = object(self)
  val z3 = Z3.Solver.mk_simple_solver ctx#z3
  method z3 = z3
  method ctx = ctx

  method push () = Z3.Solver.push z3
  method pop () = Z3.Solver.pop z3 1

  method add phi =
    Z3.Solver.add z3 [ctx#of_formula phi]

  method check () =
    match Z3.Solver.check z3 [] with
    | Z3.Solver.SATISFIABLE -> `Sat
    | Z3.Solver.UNSATISFIABLE -> `Unsat
    | Z3.Solver.UNKNOWN -> `Unknown

  method get_model : unit -> [`Sat of 'a model | `Unknown | `Unsat ] = fun () ->
    match self#check () with
    | `Sat ->
      begin match Z3.Solver.get_model z3 with
        | Some m -> `Sat (new model ctx m)
        | None -> `Unknown
      end
    | `Unsat -> `Unsat
    | `Unknown -> `Unknown
end

let is_sat ctx phi =
  let s = new solver ctx in
  s#add phi;
  s#check ()

let implies ctx phi psi =
  let s = new solver ctx in
  Z3.Solver.add s#z3 [
    ctx#of_formula phi;
    Z3.Boolean.mk_not ctx#z3 (ctx#of_formula psi)
  ];
  match s#check () with
  | `Sat -> false
  | `Unsat -> true
  | `Unknown -> raise Unknown_result

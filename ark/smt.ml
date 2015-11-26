open Syntax
open BatPervasives

include Apak.Log.Make(struct let name = "ark.smt" end)

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
    let index = Quantifier.get_index ast in
    alg (`Var (index, (typ_of_sort (Expr.get_sort ast))))
  | QUANTIFIER_AST ->
    let ast = Quantifier.quantifier_of_expr ast in
    let qt =
      if Quantifier.is_existential ast then `Exists
      else `Forall
    in
    List.fold_right2
      (fun name sort body ->
         alg (`Quantify (qt,
                         Z3.Symbol.to_string name,
                         typ_of_sort sort,
                         body)))
      (Quantifier.get_bound_variable_names ast)
      (Quantifier.get_bound_variable_sorts ast)
      (eval alg (Quantifier.get_body ast))
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

class type ['a] smt_model = object
  method eval_int : 'a term -> ZZ.t
  method eval_real : 'a term -> QQ.t
  method sat :  'a formula -> bool
  method to_string : unit -> string
end

class type ['a] smt_solver = object
  method add : ('a formula) list -> unit
  method push : unit -> unit
  method pop : int -> unit
  method reset : unit -> unit
  method check : ('a formula) list -> [ `Sat | `Unsat | `Unknown ]  
  method to_string : unit -> string
  method get_model : unit -> [ `Sat of 'a smt_model | `Unsat | `Unknown ]
  method get_unsat_core : ('a formula) list ->
    [ `Sat | `Unsat of ('a formula) list | `Unknown ]
end

class type ['a] smt_context = object
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

let z3_of_symbol z3 sym = Z3.Symbol.mk_int z3 (Obj.magic sym)

let z3_of_term ark z3 term =
  let alg = function
    | `Real qq ->
      begin match QQ.to_zz qq with
        | Some zz -> Z3.Arithmetic.Integer.mk_numeral_s z3 (ZZ.show zz)
        | None -> Z3.Arithmetic.Real.mk_numeral_s z3 (QQ.show qq)
      end
    | `Const sym ->
      let sort = match typ_symbol ark sym with
        | `TyInt -> sort_of_typ z3 `TyInt
        | `TyReal -> sort_of_typ z3 `TyReal
        | `TyBool | `TyFun (_,_) -> invalid_arg "z3_of.term"
      in
      let decl = Z3.FuncDecl.mk_const_decl z3 (z3_of_symbol z3 sym) sort in
      Z3.Expr.mk_const_f z3 decl
    | `Var (i, `TyFun (_, _)) | `Var (i, `TyBool) -> invalid_arg "z3_of.term"
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
  in
  Term.eval ark alg term

let z3_of_formula ark z3 phi =
  let of_term = z3_of_term ark z3 in
  let alg = function
    | `Tru -> Z3.Boolean.mk_true z3
    | `Fls -> Z3.Boolean.mk_false z3
    | `And conjuncts -> Z3.Boolean.mk_and z3 conjuncts
    | `Or disjuncts -> Z3.Boolean.mk_or z3 disjuncts
    | `Not phi -> Z3.Boolean.mk_not z3 phi
    | `Quantify (qt, name, typ, phi) ->
      mk_quantified z3 qt ~name typ phi
    | `Atom (`Eq, s, t) -> Z3.Boolean.mk_eq z3 (of_term s) (of_term t)
    | `Atom (`Leq, s, t) -> Z3.Arithmetic.mk_le z3 (of_term s) (of_term t)
    | `Atom (`Lt, s, t) -> Z3.Arithmetic.mk_lt z3 (of_term s) (of_term t)
    | `Proposition (`Var i) ->
      Z3.Quantifier.mk_bound z3 i (sort_of_typ z3 `TyBool)
    | `Proposition (`Const p) ->
      let decl =
        Z3.FuncDecl.mk_const_decl z3
          (z3_of_symbol z3 p)
          (sort_of_typ z3 `TyBool)
      in
      Z3.Expr.mk_const_f z3 decl
  in
  Formula.eval ark alg phi

let of_z3 context const_of_decl expr =
  let term = function
    | `Term (_, t) -> t
    | `Formula phi -> invalid_arg "of_z3.term"
  in
  let ite = function
    | `Term (ite, _) -> ite
    | `Formula phi -> invalid_arg "of_z3.term"
  in
  let ite_formula phi (sk, cond, tthen, telse) =
    let sk_def =
      mk_or context [
        mk_and context [
          cond;
          mk_eq context (mk_const context sk) tthen
        ];
        mk_and context [
          mk_not context cond;
          mk_eq context (mk_const context sk) telse
        ]
      ]
    in
    mk_exists_const context sk (mk_and context [sk_def; phi])
  in
  let ite_formula phi (sk, cond, tthen, telse) =
    mk_or context [
      mk_and context [
        cond;
        substitute_const context
          (fun k -> if k = sk then tthen else mk_const context k)
          phi
      ];
      mk_and context [
        mk_not context cond;
        substitute_const context
          (fun k -> if k = sk then telse else mk_const context k)
          phi
      ]
    ]
  in
  let formula = function
    | `Formula phi -> phi
    | _ -> invalid_arg "of_z3.formula"
  in
  let alg = function
    | `Real qq -> `Term ([], mk_real context qq)
    | `Var (i, `TyBool) -> `Formula (mk_var context i `TyBool)
    | `Var (i, typ) -> `Term ([], mk_var context i typ)
    | `App (decl, []) ->
      let const_sym = const_of_decl decl in
      begin match typ_symbol context const_sym with
        | `TyBool -> `Formula (mk_const context const_sym)
        | `TyInt | `TyReal -> `Term ([], mk_const context const_sym)
        | `TyFun (_, _) -> assert false (* Shouldn't appear with zero args *)
      end
    | `Add sum ->
      `Term (List.concat (List.map ite sum),
             mk_add context (List.map term sum))
    | `Mul product ->
      `Term (List.concat (List.map ite product),
             mk_mul context (List.map term product))
    | `Binop (op, s, t) ->
      let mk_op = match op with
        | `Div -> mk_div
        | `Mod -> mk_mod
      in
      `Term ((ite s)@(ite t), mk_op context (term s) (term t))
    | `Unop (`Floor, t) -> `Term (ite t, mk_floor context (term t))
    | `Unop (`Neg, t) -> `Term (ite t, mk_neg context (term t))
    | `Tru -> `Formula (mk_true context)
    | `Fls -> `Formula (mk_false context)
    | `And conjuncts -> `Formula (mk_and context (List.map formula conjuncts))
    | `Or disjuncts -> `Formula (mk_or context (List.map formula disjuncts))
    | `Not phi -> `Formula (mk_not context (formula phi))
    | `Quantify (`Exists, name, typ, phi) ->
      `Formula (mk_exists context ~name:name typ (formula phi))
    | `Quantify (`Forall, name, typ, phi) ->
      `Formula (mk_forall context ~name:name typ (formula phi))
    | `Atom (`Eq, `Term (ite_s, s), `Term (ite_t, t)) ->
      `Formula (List.fold_left ite_formula (mk_eq context s t) (ite_s@ite_t))
    | `Atom (`Eq, `Formula phi, `Formula psi) ->
      `Formula (mk_or context [
          mk_and context [mk_not context phi; mk_not context psi];
          mk_and context [phi; psi];
        ])
    | `Atom (`Leq, s, t) ->
      `Formula (List.fold_left
                  ite_formula
                  (mk_leq context (term s) (term t))
                  ((ite s)@(ite t)))
    | `Atom (`Lt, s, t) ->
      `Formula (List.fold_left
                  ite_formula
                  (mk_lt context (term s) (term t))
                  ((ite s)@(ite t)))
    | `Atom (`Eq, _, _) -> invalid_arg "of_z3"
    | `Ite (`Formula cond, `Formula phi, `Formula psi) ->
      let ite =
        mk_or context [
          mk_and context [cond; phi];
          mk_and context [mk_not context cond; psi]
        ]
      in
      `Formula ite
    | `Ite (cond, s, t) ->
      let typ =
        match term_typ context (term s), term_typ context (term s) with
        | `TyInt, `TyInt -> `TyInt
        | _, _ -> `TyReal
      in
      let sk = mk_symbol context ~name:"ite" typ in
      `Term ((sk, formula cond, term s, term t)::((ite s)@(ite t)),
             mk_const context sk)
    | `App (decl, args) ->
      invalid_arg ("of_z3: " ^ (Z3.FuncDecl.to_string decl))
  in
  eval alg expr

(* const_of_decl is sufficient for round-tripping, since const_sym's become
   int symbols *)
let const_of_decl decl =
  let sym = Z3.FuncDecl.get_name decl in
  assert (Z3.Symbol.is_int_symbol sym);
  Obj.magic (Z3.Symbol.get_int sym)

let term_of_z3 context term =
  match of_z3 context const_of_decl term with
  | `Term ([], t) -> t
  | _ -> invalid_arg "term_of"

let formula_of_z3 context phi =
  match of_z3 context const_of_decl phi with
  | `Formula phi -> phi
  | `Term _ -> invalid_arg "formula_of"


class ['a] z3_model (context : 'a context) z3 m =
  let of_formula = z3_of_formula context z3 in
  let of_term = z3_of_term context z3 in
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
        Apak.Log.time "solver.check" (Z3.Solver.check s) (List.map of_formula args)
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

let mk_context : 'a context -> (string * string) list -> 'a smt_context
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

  method load_smtlib2 str =
   let ast = Z3.SMT.parse_smtlib2_string z3 str [] [] [] [] in
      let const_of_decl =
        let cos =
          Apak.Memo.memo (fun (name, typ) -> mk_symbol context ~name typ)
        in
        fun decl ->
          let open Z3 in
          let sym = FuncDecl.get_name decl in
          assert (FuncDecl.get_domain decl = []);
          cos (Symbol.to_string sym, typ_of_sort (FuncDecl.get_range decl))
      in
      match of_z3 context const_of_decl ast with
      | `Formula phi -> phi
      | `Term _ -> invalid_arg "load_smtlib2"
  end

let mk_solver ?(theory="") ctx =
  if theory = "" then
    (new z3_solver ctx#ark ctx#z3 (Z3.Solver.mk_simple_solver ctx#z3))
  else
    (new z3_solver ctx#ark ctx#z3 (Z3.Solver.mk_solver_s ctx#z3 theory))

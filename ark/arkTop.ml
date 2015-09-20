open ArkAst
open Apak

module CZ = Smt.MakeSolver(Ctx)(struct let opts = [] end)()
module C = struct
  include Ctx
  include CZ
end

let load_math_formula filename =
  let open Lexing in
  let lexbuf = Lexing.from_channel (open_in filename) in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  try ArkParse.math_main ArkLex.math_token lexbuf with
  | _ ->
    let open Lexing in
    let pos = lexbuf.lex_curr_p in
    failwith (Printf.sprintf "Parse error: %s:%d:%d"
                filename
                pos.pos_lnum
                (pos.pos_cnum - pos.pos_bol + 1))

let load_math_opt filename =
  let open Lexing in
  let lexbuf = Lexing.from_channel (open_in filename) in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  try ArkParse.math_opt_main ArkLex.math_token lexbuf with
  | _ ->
    let open Lexing in
    let pos = lexbuf.lex_curr_p in
    failwith (Printf.sprintf "Parse error: %s:%d:%d"
                filename
                pos.pos_lnum
                (pos.pos_cnum - pos.pos_bol + 1))

(*
let load_smtlib2 filename =
  let open Z3 in
  let open Z3enums in
  let ctx = mk_context [] in
  let ast = SMT.parse_smtlib2_file ctx filename [] [] [] [] in
  print_endline (AST.to_string ast)
  *)
(*
  let go ast =
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
  in
  go*)

let _ =
  (*  Log.verbosity_level := `info;*)
  Log.colorize := true;
  match Sys.argv.(1) with
  | "sat" ->
    let phi = load_math_formula Sys.argv.(2) in
    begin match Abstract.aqsat (module C) phi with
      | `Sat -> Log.logf ~level:`always "Satisfiable"
      | `Unsat -> Log.logf ~level:`always "Unsatisfiable"
      | `Unknown -> Log.logf ~level:`always "Unknown"
    end
  | "sat-z3" ->
    let phi = load_math_formula Sys.argv.(2) in
    begin match CZ.is_sat phi with
      | `Sat -> Log.logf ~level:`always "Satisfiable"
      | `Unsat -> Log.logf ~level:`always "Unsatisfiable"
      | `Unknown -> Log.logf ~level:`always "Unknown"
    end
  | "sat-mbp" ->
    let phi = load_math_formula Sys.argv.(2) in
    let psi = Abstract.qe_mbp (module C) phi in
    begin match CZ.is_sat psi with
      | `Sat -> Log.logf ~level:`always "Satisfiable"
      | `Unsat -> Log.logf ~level:`always "Unsatisfiable"
      | `Unknown -> Log.logf ~level:`always "Unknown"
    end
  | "sat-z3qe" ->
    let phi = load_math_formula Sys.argv.(2) in
    begin match CZ.is_sat (CZ.qe phi) with
      | `Sat -> Log.logf ~level:`always "Satisfiable"
      | `Unsat -> Log.logf ~level:`always "Unsatisfiable"
      | `Unknown -> Log.logf ~level:`always "Unknown"
    end
  | "qe-sat" ->
    let phi = load_math_formula Sys.argv.(2) in
    let phi = Ctx.Formula.prenex phi in
    begin match CZ.qe_sat phi with
      | `Sat -> Log.logf ~level:`always "Satisfiable"
      | `Unsat -> Log.logf ~level:`always "Unsatisfiable"
      | `Unknown -> Log.logf ~level:`always "Unknown"
    end
  | "qe-sat-unbounded" ->
    let (objective, phi) = load_math_opt Sys.argv.(2) in
    let phi = Ctx.Formula.prenex phi in
    begin match CZ.qe_sat phi with
      | `Sat -> Log.logf ~level:`always "Satisfiable"
      | `Unsat -> Log.logf ~level:`always "Unsatisfiable"
      | `Unknown -> Log.logf ~level:`always "Unknown"
    end

  | "qe-mbp" ->
    let phi = load_math_formula Sys.argv.(2) in
    let psi = Abstract.qe_mbp (module C) phi in
    Log.logf ~level:`always "%a" C.Formula.pp psi
  | "opt" ->
    let (objective, phi) = load_math_opt Sys.argv.(2) in
    begin match Abstract.aqopt (module C) phi objective with
      | `Sat ivl ->
        begin match Interval.upper ivl with
          | Some upper ->
            Log.logf ~level:`always "Upper bound: %a" QQ.pp upper
          | None -> Log.logf ~level:`always "Upper bound: oo"
        end
      | `Unsat -> Log.logf ~level:`always "Unsatisfiable"
      | `Unknown -> Log.logf ~level:`always "Unknown"
    end
  | "opt-mbp" ->
    let (objective, phi) = load_math_opt Sys.argv.(2) in
    let psi = Abstract.qe_mbp (module C) phi in
    begin match C.optimize_box psi [objective] with
      | `Sat [ivl] ->
        begin match Interval.upper ivl with
          | Some upper ->
            Log.logf ~level:`always "Upper bound: %a" QQ.pp upper
          | None -> Log.logf ~level:`always "Upper bound: oo"
        end
      | `Unsat -> Log.logf ~level:`always "Unsatisfiable"
      | `Unknown -> Log.logf ~level:`always "Unknown"
      | _ -> assert false
    end
  | "opt-z3qe" ->
    let (objective, phi) = load_math_opt Sys.argv.(2) in
    let psi = CZ.qe phi in
    begin match C.optimize_box psi [objective] with
      | `Sat [ivl] ->
        begin match Interval.upper ivl with
          | Some upper ->
            Log.logf ~level:`always "Upper bound: %a" QQ.pp upper
          | None -> Log.logf ~level:`always "Upper bound: oo"
        end
      | `Unsat -> Log.logf ~level:`always "Unsatisfiable"
      | `Unknown -> Log.logf ~level:`always "Unknown"
      | _ -> assert false
    end
  | x -> Log.fatalf "Unknown command: `%s'" x

open ArkAst
open Apak
open ArkApron

module Ctx = ArkAst.Ctx
module Infix = Syntax.Infix(Ctx)
let ctx = Ctx.context
let smt_ctx = ArkZ3.mk_context ctx [("model", "true");
                                    ("unsat_core", "true")]

let file_contents filename =
  let chan = open_in filename in
  let len = in_channel_length chan in
  let buf = Bytes.create len in
  really_input chan buf 0 len;
  close_in chan;
  buf

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

let load_smtlib2 filename = smt_ctx#load_smtlib2 (file_contents filename)

let load_formula filename =
  if Filename.check_suffix filename "m" then load_math_formula filename
  else if Filename.check_suffix filename "smt2" then load_smtlib2 filename
  else Log.fatalf "Unrecognized file extension for %s" filename

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

let print_result = function
  | `Sat -> Log.logf ~level:`always "sat"
  | `Unsat -> Log.logf ~level:`always "unsat"
  | `Unknown -> Log.logf ~level:`always "unknown"

let _ =
  Log.colorize := true;
  let i =
    match Sys.argv.(1) with
    | "verbose" -> Log.verbosity_level := `info; 2
    | "trace" -> Log.verbosity_level := `trace; 2
    | _ -> 1
  in
  match Sys.argv.(i) with
  | "sat" ->
    let phi = load_formula Sys.argv.(i+1) in
    print_result (Quantifier.simsat ctx phi)
    (*    Apak.Log.print_stats ()*)

  | "sat-forward" ->
    let phi = load_formula Sys.argv.(i+1) in
    print_result (Quantifier.simsat_forward ctx phi)

  | "easysat" ->
    let phi = load_formula Sys.argv.(i+1) in
    print_result (Quantifier.easy_sat ctx phi)

  | "sat-z3" ->
    let phi = load_formula Sys.argv.(i+1) in
    print_result (smt_ctx#is_sat phi)
  | "sat-mbp" ->
    let phi = load_formula Sys.argv.(i+1) in
    let psi = Quantifier.qe_mbp ctx phi in
    print_result (smt_ctx#is_sat psi)
  | "sat-z3qe" ->
    let phi = load_formula Sys.argv.(i+1) in
    print_result (smt_ctx#is_sat (smt_ctx#qe phi))
  | "qsat" ->
    let str = file_contents Sys.argv.(i+1) in

    let z3 = Z3.mk_context [] in
    let t =
      Z3.Tactic.and_then z3
        (ArkZ3.mk_quantifier_simplify_tactic z3)
        (Z3.Tactic.mk_tactic z3 "qsat")
        []
    in
    let s = Z3.Solver.mk_solver_t z3 t in
    Z3.Solver.add s [Z3.SMT.parse_smtlib2_string z3 str [] [] [] []];
    begin match Z3.Solver.check s [] with
    | Z3.Solver.SATISFIABLE -> print_endline "sat"
    | Z3.Solver.UNSATISFIABLE -> print_endline "unsat"
    | Z3.Solver.UNKNOWN -> print_endline "unknown"
    end

  | "qe-sat-unbounded" ->
    let (objective, phi) = load_math_opt Sys.argv.(i+1) in
    let phi = Syntax.Formula.prenex ctx phi in
    print_result (smt_ctx#qe_sat phi)

  | "qe-mbp" ->
    let phi = load_formula Sys.argv.(i+1) in
    let psi = Quantifier.qe_mbp ctx phi in
    Log.logf ~level:`always "%a" (Syntax.Formula.pp ctx) psi
  | "opt" ->
    let (objective, phi) = load_math_opt Sys.argv.(i+1) in
    begin match Quantifier.maximize ctx phi objective with
      | `Bounded b ->
        Log.logf ~level:`always "Upper bound: %a" QQ.pp b;
      | `Infinity ->
        Log.logf ~level:`always "Upper bound: oo"
      | `MinusInfinity ->
        Log.logf ~level:`always "Upper bound: -oo"
      | `Unknown ->
        Log.logf ~level:`always "Upper bound: unknown"
    end
  | "opt-mbp" ->
    let (objective, phi) = load_math_opt Sys.argv.(i+1) in
    let psi = Quantifier.qe_mbp ctx phi in
    begin match smt_ctx#optimize_box psi [objective] with
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
    let (objective, phi) = load_math_opt Sys.argv.(i+1) in
    let psi = smt_ctx#qe phi in
    begin match smt_ctx#optimize_box psi [objective] with
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
  | "echo" ->
    Z3.SMT.benchmark_to_smtstring
      smt_ctx#z3
      (Sys.argv.(i+1))
      ""
      "unknown"
      ""
      []
      (smt_ctx#of_formula (load_formula Sys.argv.(i+1)))
    |> print_endline

  | "stats" ->
    let open Syntax in
    let phi = load_formula Sys.argv.(i+1) in
    let phi = Formula.prenex ctx phi in
    let constants = fold_constants Symbol.Set.add phi Symbol.Set.empty in
    let rec go phi =
      match Formula.destruct ctx phi with
      | `Quantify (`Exists, name, typ, psi) -> "E" ^ (go psi)
      | `Quantify (`Forall, name, typ, psi) -> "A" ^ (go psi)
      | _ -> ""
    in
    let qf_pre =
      (String.concat ""
         (List.map (fun _ -> "E") (Symbol.Set.elements constants)))
      ^ (go phi)
    in
    Log.logf ~level:`always "Quantifier prefix: %s" qf_pre;
    Log.logf ~level:`always "Variables: %d" (String.length qf_pre);
    Log.logf ~level:`always "Matrix size: %d" (size phi)

  | "random" ->
    Random.self_init ();
    let qf_pre = ref [] in
    String.iter (function
        | 'E' -> qf_pre := `Exists::(!qf_pre)
        | 'A' -> qf_pre := `Forall::(!qf_pre)
        | _ -> assert false)
      Sys.argv.(i+1);
    RandomFormula.quantifier_prefix := List.rev (!qf_pre);
    RandomFormula.formula_uq_depth := int_of_string (Sys.argv.(i + 2));
    begin
      match Sys.argv.(i + 3) with
      | "dense" -> RandomFormula.dense := true;
      | "sparse" -> RandomFormula.dense := false;
      | _ -> assert false
    end;
    Z3.SMT.benchmark_to_smtstring
      smt_ctx#z3
      "random"
      ""
      "unknown"
      ""
      []
      (smt_ctx#of_formula (RandomFormula.mk_random_formula ctx))
    |> print_endline

  | "sat-nonlinear" ->
    let phi = load_formula Sys.argv.(i+1) in
    print_result (Abstract.is_sat ctx (snd (Quantifier.normalize ctx phi)))

  | x -> Log.fatalf "Unknown command: `%s'" x

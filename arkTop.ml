open ArkAst
open Apak

module Ctx = ArkAst.Ctx
module Infix = Syntax.Infix(Ctx)
let ctx = Ctx.context
let smt_ctx = Smt.mk_context ctx []

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
    print_result (Abstract.aqsat smt_ctx phi)
  | "sat-z3" ->
    let phi = load_formula Sys.argv.(i+1) in
    print_result (smt_ctx#is_sat phi)
  | "sat-mbp" ->
    let phi = load_formula Sys.argv.(i+1) in
    let psi = Abstract.qe_mbp smt_ctx phi in
    print_result (smt_ctx#is_sat psi)
  | "sat-z3qe" ->
    let phi = load_formula Sys.argv.(i+1) in
    print_result (smt_ctx#is_sat (smt_ctx#qe phi))
  | "qsat" ->
    let str = file_contents Sys.argv.(i+1) in

    let z3 = Z3.mk_context [] in
    let t =
      Z3.Tactic.and_then z3
        (Smt.mk_quantifier_simplify_tactic z3)
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
    let psi = Abstract.qe_mbp smt_ctx phi in
    Log.logf ~level:`always "%a" (Syntax.Formula.pp ctx) psi
  | "opt" ->
    let (objective, phi) = load_math_opt Sys.argv.(i+1) in
    begin match Abstract.aqopt smt_ctx phi objective with
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
    let (objective, phi) = load_math_opt Sys.argv.(i+1) in
    let psi = Abstract.qe_mbp smt_ctx phi in
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

  | x -> Log.fatalf "Unknown command: `%s'" x

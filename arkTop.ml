open ArkAst
open Apak

module CZ = Smt.MakeSolver(Ctx)(struct let opts = [] end)()
module C = struct
  include Ctx
  include CZ
end

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

let load_smtlib2 filename = CZ.load_smtlib2 (file_contents filename)

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
    begin match Abstract.aqsat (module C) phi with
      | `Sat -> Log.logf ~level:`always "Satisfiable"
      | `Unsat -> Log.logf ~level:`always "Unsatisfiable"
      | `Unknown -> Log.logf ~level:`always "Unknown"
    end
  | "sat-z3" ->
    let phi = load_formula Sys.argv.(i+1) in
    begin match CZ.is_sat phi with
      | `Sat -> Log.logf ~level:`always "Satisfiable"
      | `Unsat -> Log.logf ~level:`always "Unsatisfiable"
      | `Unknown -> Log.logf ~level:`always "Unknown"
    end
  | "sat-mbp" ->
    let phi = load_formula Sys.argv.(i+1) in
    let psi = Abstract.qe_mbp (module C) phi in
    begin match CZ.is_sat psi with
      | `Sat -> Log.logf ~level:`always "Satisfiable"
      | `Unsat -> Log.logf ~level:`always "Unsatisfiable"
      | `Unknown -> Log.logf ~level:`always "Unknown"
    end
  | "sat-z3qe" ->
    let phi = load_formula Sys.argv.(i+1) in
    begin match CZ.is_sat (CZ.qe phi) with
      | `Sat -> Log.logf ~level:`always "Satisfiable"
      | `Unsat -> Log.logf ~level:`always "Unsatisfiable"
      | `Unknown -> Log.logf ~level:`always "Unknown"
    end
  | "qe-sat" ->
    let phi = load_formula Sys.argv.(i+1) in
    let phi = Ctx.Formula.prenex phi in
    begin match CZ.qe_sat phi with
      | `Sat -> Log.logf ~level:`always "Satisfiable"
      | `Unsat -> Log.logf ~level:`always "Unsatisfiable"
      | `Unknown -> Log.logf ~level:`always "Unknown"
    end
  | "qe-sat-unbounded" ->
    let (objective, phi) = load_math_opt Sys.argv.(i+1) in
    let phi = Ctx.Formula.prenex phi in
    begin match CZ.qe_sat phi with
      | `Sat -> Log.logf ~level:`always "Satisfiable"
      | `Unsat -> Log.logf ~level:`always "Unsatisfiable"
      | `Unknown -> Log.logf ~level:`always "Unknown"
    end

  | "qe-mbp" ->
    let phi = load_formula Sys.argv.(i+1) in
    let psi = Abstract.qe_mbp (module C) phi in
    Log.logf ~level:`always "%a" C.Formula.pp psi
  | "opt" ->
    let (objective, phi) = load_math_opt Sys.argv.(i+1) in
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
    let (objective, phi) = load_math_opt Sys.argv.(i+1) in
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
    let (objective, phi) = load_math_opt Sys.argv.(i+1) in
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

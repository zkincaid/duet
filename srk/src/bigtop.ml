open SrkAst
open SrkApron
open Syntax

module Ctx = SrkAst.Ctx
module Infix = Syntax.Infix(Ctx)
let srk = Ctx.context

let generator_rep = ref false

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
  try SrkParse.math_main SrkLex.math_token lexbuf with
  | _ ->
    let open Lexing in
    let pos = lexbuf.lex_curr_p in
    failwith (Printf.sprintf "Parse error: %s:%d:%d"
                filename
                pos.pos_lnum
                (pos.pos_cnum - pos.pos_bol + 1))

let load_smtlib2 filename =
  SrkZ3.load_smtlib2 srk (Bytes.to_string (file_contents filename))

let load_formula filename =
  if Filename.check_suffix filename "m" then load_math_formula filename
  else if Filename.check_suffix filename "smt2" then load_smtlib2 filename
  else Log.fatalf "Unrecognized file extension for %s" filename

let load_math_opt filename =
  let open Lexing in
  let lexbuf = Lexing.from_channel (open_in filename) in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  try SrkParse.math_opt_main SrkLex.math_token lexbuf with
  | _ ->
    let open Lexing in
    let pos = lexbuf.lex_curr_p in
    failwith (Printf.sprintf "Parse error: %s:%d:%d"
                filename
                pos.pos_lnum
                (pos.pos_cnum - pos.pos_bol + 1))

let print_result = function
  | `Sat -> Format.printf "sat@\n"
  | `Unsat -> Format.printf "unsat@\n"
  | `Unknown -> Format.printf "unknown@\n"

let spec_list = [
  ("-simsat",
   Arg.String (fun file ->
       let phi = load_formula file in
       print_result (Quantifier.simsat_forward srk phi)),
   " Test satisfiability of an LRA or LIA formula (IJCAI'16)");

  ("-nlsat",
   Arg.String (fun file ->
       let phi = load_formula file in
       print_result (Wedge.is_sat srk (snd (Quantifier.normalize srk phi)))),
   " Test satisfiability of a non-linear ground formula (POPL'18)");

  ("-generator",
   Arg.Set generator_rep,
   " Print generator representation of convex hull");

  ("-convex-hull",
   Arg.String (fun file ->
       let (qf, phi) = Quantifier.normalize srk (load_formula file) in
       if List.exists (fun (q, _) -> q = `Forall) qf then
         failwith "universal quantification not supported";
       let exists v =
         not (List.exists (fun (_, x) -> x = v) qf)
       in
       let polka = Polka.manager_alloc_strict () in
       let pp_hull formatter hull =
         if !generator_rep then begin
           let env = SrkApron.get_env hull in
           let dim = SrkApron.Env.dimension env in
           Format.printf "Symbols:   [%a]@\n@[<v 0>"
             (SrkUtil.pp_print_enum (Syntax.pp_symbol srk)) (SrkApron.Env.vars env);
           SrkApron.generators hull
           |> List.iter (fun (generator, typ) ->
               Format.printf "%s [@[<hov 1>"
                 (match typ with
                  | `Line    -> "line:     "
                  | `Vertex  -> "vertex:   "
                  | `Ray     -> "ray:      "
                  | `LineMod -> "line mod: "
                  | `RayMod  -> "ray mod:  ");
               for i = 0 to dim - 2 do
                 Format.printf "%a@;" QQ.pp (Linear.QQVector.coeff i generator)
               done;
               Format.printf "%a]@]@;" QQ.pp (Linear.QQVector.coeff (dim - 1) generator));
           Format.printf "@]"
         end else
           SrkApron.pp formatter hull
       in
       Format.printf "Convex hull:@\n @[<v 0>%a@]@\n"
         pp_hull (Abstract.abstract ~exists srk polka phi)),
   " Compute the convex hull of an existential linear arithmetic formula");

  ("-wedge-hull",
   Arg.String (fun file ->
       let (qf, phi) = Quantifier.normalize srk (load_formula file) in
       if List.exists (fun (q, _) -> q = `Forall) qf then
         failwith "universal quantification not supported";
       let exists v =
         not (List.exists (fun (_, x) -> x = v) qf)
       in
       let wedge = Wedge.abstract ~exists srk phi in
       Format.printf "Wedge hull:@\n @[<v 0>%a@]@\n" Wedge.pp wedge),
   " Compute the wedge hull of an existential non-linear arithmetic formula");

  ("-affine-hull",
   Arg.String (fun file ->
       let phi = load_formula file in
       let (qf, psi) = Quantifier.normalize srk phi in
       if List.exists (fun (q, _) -> q = `Forall) qf then
         failwith "universal quantification not supported";
       let symbols = (* omits skolem constants *)
         Symbol.Set.elements (symbols phi)
       in
       let aff_hull = Abstract.affine_hull srk phi symbols in
       Format.printf "Affine hull:@\n %a@\n"
         (SrkUtil.pp_print_enum (Term.pp srk)) (BatList.enum aff_hull)),
   " Compute the affine hull of an existential linear arithmetic formula");

  ("-stats",
   Arg.String (fun file ->
       let open Syntax in
       let phi = load_formula file in
       let phi = Formula.prenex srk phi in
       let constants = fold_constants Symbol.Set.add phi Symbol.Set.empty in
       let rec go phi =
         match Formula.destruct srk phi with
         | `Quantify (`Exists, name, typ, psi) -> "E" ^ (go psi)
         | `Quantify (`Forall, name, typ, psi) -> "A" ^ (go psi)
         | _ -> ""
       in
       let qf_pre =
         (String.concat ""
            (List.map (fun _ -> "E") (Symbol.Set.elements constants)))
         ^ (go phi)
       in
       Format.printf "Quantifier prefix: %s" qf_pre;
       Format.printf "Variables: %d" (String.length qf_pre);
       Format.printf "Matrix size: %d" (size phi)),
   " Print formula statistics");

  ("-random",
   Arg.Tuple [
     Arg.String (fun arg ->
         let qf_pre = ref [] in
         String.iter (function
             | 'E' -> qf_pre := `Exists::(!qf_pre)
             | 'A' -> qf_pre := `Forall::(!qf_pre)
             | _ -> assert false)
           arg;
         RandomFormula.quantifier_prefix := List.rev (!qf_pre));
     Arg.Set_int RandomFormula.formula_uq_depth;
     Arg.String (fun arg ->
         begin match arg with
         | "dense" -> RandomFormula.dense := true
         | "sparse" -> RandomFormula.dense := false
         | x -> Log.fatalf "unknown argument: %s" x;
         end;
         Random.self_init ();
         let z3 = Z3.mk_context [] in
         Z3.SMT.benchmark_to_smtstring
           z3
           "random"
           ""
           "unknown"
           ""
           []
           (SrkZ3.z3_of_formula srk z3 (RandomFormula.mk_random_formula srk))
         |> print_endline)
   ],
   " Generate a random formula");

  ("-verbosity",
   Arg.String (fun v -> Log.verbosity_level := (Log.level_of_string v)),
   " Set verbosity level (higher = more verbose; defaults to 0)");

  ("-verbose",
   Arg.String (fun v -> Log.set_verbosity_level v `info),
   " Raise verbosity for a particular module");

  ("-verbose-list",
   Arg.Unit (fun () ->
       print_endline "Available modules for setting verbosity:";
       Hashtbl.iter (fun k _ ->
           print_endline (" - " ^ k);
         ) Log.loggers;
       exit 0;
     ),
   " List modules which can be used with -verbose")
]

let usage_msg = "bigtop: command line interface to srk \n\
  Usage:\n\
  \tbigtop [options] [-simsat|-nlsat] formula.smt2\n\
  \tbigtop [-generator] -convex-hull formula.smt2\n\
  \tbigtop -affine-hull formula.smt2\n\
  \tbigtop -wedge-hull formula.smt2\n\
  \tbigtop -stats formula.smt2\n\
  \tbigtop -random (A|E)* depth [dense|sparse]\n"

let anon_fun s = failwith ("Unknown option: " ^ s)

let () =
  if Array.length Sys.argv == 1 then
    Arg.usage (Arg.align spec_list) usage_msg
  else
    Arg.parse (Arg.align spec_list) anon_fun usage_msg

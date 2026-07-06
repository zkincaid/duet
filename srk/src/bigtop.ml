open Srk
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

let load_chc fp filename = Chc.ChcSrkZ3.parse_file srk fp filename

let load_formula filename =
  let formula =
    if Filename.check_suffix filename "m" then load_math_formula filename
    else if Filename.check_suffix filename "smt2" then load_smtlib2 filename
    else Log.fatalf "Unrecognized file extension for %s" filename
  in
  Nonlinear.ensure_symbols srk;
  let subst f =
    match typ_symbol srk f with
    | `TyReal | `TyInt | `TyBool | `TyArr -> mk_const srk f
    | `TyFun (args, _) ->
      let f =
        try get_named_symbol srk (show_symbol srk f)
        with Not_found -> f
      in
      mk_app srk f (List.mapi (fun i typ -> mk_var srk i typ) args)
  in
  substitute_sym srk subst formula

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

module Retype : sig

  (* `LiraToLra
    - First compute an equivalent formula in the language of LRA
      (LRA terms, LRA atoms) free of floor, mod, div and is_int.
    - Then replace all integer variables with real ones.

    `LiraToLia:
    - `JustSymbols: just replace real variables with integer ones;
    - `LraTerms: in addition with floor, mod, div removed;
    - `LraFormula: in addition with [is_int] removed.

    Integralization uses the last, i.e., first compute an equivalent formula
    in the language of LRA, free of floor, mod, div, and is_int,
    then replace all real variables with integer ones.
   *)
  val retype_formula:
    'a context ->
    [ `LiraToLra
    | `LiraToLia of [`JustSymbols | `LraTerms | `LraFormula]] ->
    'a formula -> 'a formula * bool

end = struct
  module S = Syntax.Symbol.Set

  let retype srk (fromto: [`IntToReal | `RealToInt]) expr =
    let table = Hashtbl.create 991 in
    let retyped_symbol sym =
      begin match fromto with
      | `IntToReal ->
         mk_symbol srk ~name:(Format.asprintf "%s_realified"
                                (show_symbol srk sym))
           `TyReal
      | `RealToInt ->
         mk_symbol srk ~name:(Format.asprintf "%s_integralized"
                                (show_symbol srk sym))
           `TyInt
      end
    in
    let lookup s = begin try Hashtbl.find table s with
      | Not_found ->
        begin match (typ_symbol srk s, fromto) with
        | (`TyInt, `IntToReal)
          | (`TyReal, `RealToInt) ->
          let new_sym = retyped_symbol s in
          Hashtbl.add table s new_sym;
          new_sym
        | _ -> s
        end
      end
    in
    (substitute_const srk (fun s -> mk_const srk (lookup s)) expr, table)

  let retype_quantifier_free srk how phi =
    let retype fml =
      match how with
      | `LiraToLra -> retype srk `IntToReal fml
      | `LiraToLia _ -> retype srk `RealToInt fml
    in
    let preprocess fml =
      match how with
      | `LiraToLra -> Syntax.eliminate_floor_mod_div srk fml
        |> Syntax.eliminate_is_int srk
      | `LiraToLia `LraTerms -> Syntax.eliminate_floor_mod_div srk fml
      | `LiraToLia `LraFormula -> Syntax.eliminate_floor_mod_div srk fml
        |> Syntax.eliminate_is_int srk
      | `LiraToLia `JustSymbols -> fml
    in
    let processed_phi =
      Syntax.eliminate_ite srk phi
      |> rewrite srk ~down:(pos_rewriter srk)
      |> preprocess in
    let introduced_symbols = S.diff (symbols processed_phi) (symbols phi) in
    let (retyped_processed, table) = retype processed_phi in
    let remap_symbols s =
      match Hashtbl.find_opt table s with
      | Some new_sym -> new_sym
      | None -> s
    in
    let introduced_symbols' =
      introduced_symbols |> S.map remap_symbols
    in
    let equivalent = (Hashtbl.length table == 0) in
    (retyped_processed, introduced_symbols', remap_symbols, equivalent)

  let retype_formula srk
        (how : [ `LiraToLra
               | `LiraToLia of [`JustSymbols | `LraTerms | `LraFormula]])
        phi =
    let (qf, phi) = Quantifier.normalize srk phi in
    let requantify quantifiers phi =
      List.fold_left
        (fun phi sym ->
          mk_exists_const srk sym phi)
        phi
        (List.rev quantifiers)
    in
    if List.exists (fun (q, _) -> q = `Forall) qf then
      failwith "universal quantification not supported"
    else
      let (phi', introduced_symbols, remap, equivalent) =
        retype_quantifier_free srk how phi in
      let new_quantified_symbols =
        let retyped_original = List.map (fun (_, sym) -> remap sym) qf in
        retyped_original @ S.to_list introduced_symbols
      in
      ( requantify new_quantified_symbols phi', equivalent )

end

module Plt = PolyhedronLatticeTiling

module ConvHull : sig

  val print_convex_hull: 'a context
    -> (
      man:DD.closed Apron.Manager.t
      -> 'a Syntax.arith_term array
      -> 'a Plt.ConvexHull.lira_to_polyhedron_abs
    )
    -> 'a formula -> unit

end = struct

  module S = Syntax.Symbol.Set

  let pp_symbols fmt set =
    Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "@\n")
      (fun fmt sym ->
        Format.fprintf fmt "%a: %a"
          (Syntax.pp_symbol srk) sym pp_typ (typ_symbol srk sym))
      fmt (S.to_list set)

  let term_of_vector srk term_of_dim v =
    let open Syntax in
    Linear.QQVector.enum v
    |> BatEnum.fold
         (fun summands (coeff, dim) ->
           if dim <> Linear.const_dim then
             mk_mul srk [mk_real srk coeff; term_of_dim dim] :: summands
           else
             mk_real srk coeff :: summands)
         []
    |> mk_add srk

  let formula_p srk term_of_dim (kind, v) =
    let t = term_of_vector srk term_of_dim v in
    match kind with
    | `Zero -> mk_eq srk t (mk_zero srk)
    | `Nonneg -> mk_leq srk (mk_zero srk) t
    | `Pos -> mk_lt srk (mk_zero srk) t

  let formula_of_dd srk term_of_dim dd =
    DD.enum_constraints dd
    |> BatEnum.fold
         (fun atoms (kind, v) ->
           formula_p srk term_of_dim (kind, v) :: atoms) []
    |> List.rev
    |> mk_and srk

  let print_convex_hull srk mk_local_abs phi =
    let (qf, phi) = Quantifier.normalize srk phi in
    if List.exists (fun (q, _) -> q = `Forall) qf then
      failwith "universal quantification not supported";
    let quantified_symbols = List.map (fun (_, sym) -> sym) qf in
    let original_symbols_to_keep =
      S.diff (symbols phi) (S.of_list quantified_symbols) in
    let symbols_to_eliminate = S.of_list quantified_symbols in
    Format.printf "Quantified symbols: %a\n"
      (Format.pp_print_list ~pp_sep:Format.pp_print_space
         (fun fmt (_, sym) -> (Syntax.pp_symbol srk) fmt sym)) qf;

    let symbols = Syntax.symbols phi in
    let symbols_to_keep = S.diff symbols symbols_to_eliminate in
    assert (S.cardinal symbols_to_keep = S.cardinal original_symbols_to_keep);
    let terms =
      List.map (Syntax.mk_const srk) (S.to_list original_symbols_to_keep)
      (* Order matters, and we map using the order of original symbols to allow
         comparison between methods *)
      |> Array.of_list
    in
    let print_input () =
      Format.printf "Taking convex hull of formula: @[%a@]@;"
        (Syntax.Formula.pp srk) phi;
      Format.printf "Symbols to keep: @[%a@]@;" pp_symbols symbols_to_keep;
      Format.printf "Symbols to eliminate: @[%a@]@;"
        pp_symbols symbols_to_eliminate;
    in
    print_input ();
    let man = Polka.manager_alloc_loose () in
    let solver = Abstract.Solver.make srk ~theory:`LIRA phi in
    let local_abs = mk_local_abs ~man terms in
    let result = Abstract.ClosedConvexHull.abstract_by ~man solver
      (`LIRA local_abs) terms
    in
    Format.printf "Convex hull:@\n @[<v 0>%a@]@\n"
      (Syntax.Formula.pp srk)
      (formula_of_dd srk (fun dim -> terms.(dim)) result)

end


let spec_list = [
  ("-simsat",
   Arg.String (fun file ->
       let phi = load_formula file in
       print_result (Quantifier.simsat srk phi)),
   " Test satisfiability of an LRA or LIA formula (IJCAI'16)");

  ("-nlsat",
   Arg.String (fun file ->
       let phi = load_formula file in
       print_result (Wedge.is_sat srk (snd (Quantifier.normalize srk phi)))),
   " Test satisfiability of a non-linear ground formula (POPL'18)");

  ("-lirrsat",
   Arg.String (fun file ->
       let phi = load_formula file in
       print_result (Lirr.is_sat srk (snd (Quantifier.normalize srk phi)))),
   " Test satisfiability of a non-linear ground formula using theory of linear integer real rings");

  ("-normaliz",
   Arg.Unit (fun () -> PolynomialConeCpClosure.set_cutting_plane_method `Normaliz),
   " Set weak theory solver to use Normaliz's integer hull computation (instead of Gomory-Chvatal");

  ("-generator",
   Arg.Set generator_rep,
   " Print generator representation of convex hull");

  ("-lira-convex-hull"
  , Arg.String
      (fun file ->
          ConvHull.print_convex_hull srk
            (Plt.ConvexHull.cch_lira srk) (load_formula file)
      )
  , " Compute the convex hull of an existential formula in LIRA using the join of -lira-convex-hull-pc and -lira-convex-hull-lplh"
  );

  ("-lia-convex-hull"
  , Arg.String
      (fun file ->
        ConvHull.print_convex_hull srk
          (Plt.ConvexHull.cch_lia srk) (load_formula file)
      )
  , " Compute the convex hull of an existential formula in linear integer arithmetic."
  );

  ("-lra-convex-hull"
  , Arg.String
      (fun file ->
        ConvHull.print_convex_hull srk
          (Plt.ConvexHull.cch_lra srk) (load_formula file)
      )
  , " Compute the convex hull of an existential formula in linear rational arithmetic."
  );

  ("-integralize-smt-file"
  , Arg.String
      (fun file ->
        let () =
          if not (Filename.check_suffix file ".smt2") then failwith "not an SMT file"
          else ()
        in
        let phi = load_smtlib2 file in
        let (phi', equivalent) =
          try Retype.retype_formula srk (`LiraToLia `LraFormula) phi
          with
          | _ -> Format.printf "Fail at file: %s" file;
                 failwith "Failed"
        in
        Format.printf "Integralization is %s@\n"
          (if equivalent then "equivalent" else "not equivalent" )
        ;
        pp_smtlib2 srk Format.std_formatter phi'
      )
  , " Given <file>.smt as input, output file <file>_integralized.smt2 that \
      contains the integralized version of the formula in <file>.smt2"
  );

  ("-realify-smt-file"
  , Arg.String (fun file ->
        let () =
          if not (Filename.check_suffix file ".smt2") then failwith "not an SMT file"
          else ()
        in
        let phi = load_smtlib2 file in
        let (phi', equivalent) =
          try Retype.retype_formula srk `LiraToLra phi
          with
          | _ -> Format.printf "Fail at file: %s" file;
                 failwith "Failed"
        in
        Format.printf "Integralization is %s@\n"
          (if equivalent then "equivalent" else "not equivalent" )
        ;
        pp_smtlib2 srk Format.std_formatter phi'
      )
  , " Given <file>.smt as input, output file <file>_realified.smt2 that \
      contains the real relaxation of the formula in <file>.smt2"
  );

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
       let qf = fst (Quantifier.normalize srk phi) in
       if List.exists (fun (q, _) -> q = `Forall) qf then
         failwith "universal quantification not supported";
       let symbols = (* omits skolem constants *)
         Symbol.Set.elements (symbols phi)
       in
       let aff_hull = Abstract.affine_hull srk phi symbols in
       Format.printf "Affine hull:@\n %a@\n"
         (SrkUtil.pp_print_enum (ArithTerm.pp srk)) (BatList.enum aff_hull)),
   " Compute the affine hull of an existential linear arithmetic formula");

  ("-qe",
   Arg.String (fun file ->
       let open Syntax in
       let phi = load_formula file in
       let result =
         Quantifier.qe_mbp srk phi
         |> SrkSimplify.simplify_dda srk
       in
       Format.printf "%a@\n" (pp_smtlib2 srk) result),
   " Eliminate quantifiers");

  ("-stats",
   Arg.String (fun file ->
       let open Syntax in
       let phi = load_formula file in
       let phi = Formula.prenex srk phi in
       let constants = fold_constants Symbol.Set.add phi Symbol.Set.empty in
       let rec go phi =
         match Formula.destruct srk phi with
         | `Quantify (`Exists, _, _, psi) -> "E" ^ (go psi)
         | `Quantify (`Forall, _, _, psi) -> "A" ^ (go psi)
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

  ("-chc",
   Arg.String (fun file ->
       let open Iteration in
       let fp = Chc.Fp.create () in
       let fp = load_chc fp file in
       let pd =
         Iteration.product [LossyTranslation.exp; PolyhedronGuard.exp]
       in (*TODO: let user pick iter operation*)
       let rels = Chc.Fp.get_relations_used fp in
       let sln = Chc.Fp.solve srk fp pd in
       Format.printf "(Solution is:\n@[";
       SrkUtil.pp_print_enum
         ~pp_sep:(fun formatter () -> Format.fprintf formatter "@ \n ")
         (fun formatter rel ->
            let syms, phi = sln rel in
            let syms = BatArray.to_list syms in
            Format.fprintf formatter "@%a : %a@"
            (Chc.pp_rel_atom srk fp)
            (Chc.mk_rel_atom srk fp rel syms)
            (Formula.pp srk)
            phi)
         Format.std_formatter
         (Chc.Relation.Set.enum rels)),
   " Output solution to system of constrained horn clauses");

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
  \tbigtop -qe formula.smt2\n\
  \tbigtop -stats formula.smt2\n\
  \tbigtop -random (A|E)* depth [dense|sparse]\n\
  \tbigtop -reachable-goal chc.smt2\n"

let anon_fun s = failwith ("Unknown option: " ^ s)

let () =
  if Array.length Sys.argv == 1 then
    Arg.usage (Arg.align spec_list) usage_msg
  else
    Arg.parse (Arg.align spec_list) anon_fun usage_msg

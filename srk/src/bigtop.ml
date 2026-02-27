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

module Plt = PolyhedronLatticeTiling

module ConvHull : sig

  type lira_abstraction =
  | PolyReccone
    (** Local projection of the subpolyhedron contained in the
        integer class of model (roughly) + (i.e., Minkowski sum)
        recession cone of the local projection of the
        Loos-Weispfenning MBP subpolyhedron.
     *)
  | LiraLPLH of QQ.t option
    (** Local projection of the PLT followed by taking local hull (via HKMMZ) *)
  | PolyReccone_LPLH of QQ.t option
    (** The same as PolyReccone, but joined with the local hull
        (LH; via HKMMZ) of the local projection (LP) of the PLT.
        Strict inequalities are rounded to loose ones by shifting
        using the option; if unspecified, some internal choice is made.
     *)

  (** LIA abstraction requires that every variable is integer-valued
      and that the target terms have integer coefficients.
   *)
  type lia_abstraction =
    | HullThenProject of [`GomoryChvatal | `Normaliz]
    (** Baseline. Formula should not have [is_int] literals. *)
    | LiaLPLH
    (** Local projection of PLT followed by taking local hull. *)

  (** LRA abstraction ignores all [is_int] constraints in the implicant and
      integrality of variables.
   *)
  type lra_abstraction =
    | FullProject
    (** Baseline  *)
    | LwMbp
    (** Local projection of Loos-Weispfenning MBP subpolyhedron *)

  type abstraction_algorithm =
    | LiraCCH of lira_abstraction
    | LiaCCH of lia_abstraction
    | LraCCH of lra_abstraction

  val dd_subset: DD.closed DD.t -> DD.closed DD.t -> bool

  (* Both [`JustLraFormula] and [`Realified] purify the formula to get an LRA formula,
     but the latter also replace integer symbols with real ones.
   *)
  type real_relaxation = NoRelax | JustLraFormula | Realified

  val relax_to_real: real_relaxation ref

  val convex_hull: 'a context ->
                   abstraction_algorithm -> 'a formula -> DD.closed DD.t

  val compare:
    'a context ->
    (DD.closed DD.t -> DD.closed DD.t -> bool) ->
    abstraction_algorithm * real_relaxation ->
    abstraction_algorithm * real_relaxation ->
    'a formula -> unit

  (* `LiraToLra
     - Remove floor, mod, div, is_int, and replace all real variables with integer ones

     `LiraToLia:
     - `JustSymbols: just replace real variables with integer ones;
     - `LraTerms: in addition with floor, mod, div removed;
     - `LraFormula: in addition with [is_int] removed.

     For `IntToReal, floor-mod-div-ints are always removed to get an LRA formula.
   *)
  val retype_formula:
    'a context ->
    [ `LiraToLra
    | `LiraToLia of [`JustSymbols | `LraTerms | `LraFormula]] ->
    'a formula -> 'a formula * bool

end = struct

  type lira_abstraction =
  | PolyReccone
  | LiraLPLH of QQ.t option
  | PolyReccone_LPLH of QQ.t option

  type lia_abstraction =
    | HullThenProject of [`GomoryChvatal | `Normaliz]
    | LiaLPLH

  type lra_abstraction =
    | FullProject
    | LwMbp

  type abstraction_algorithm =
    | LiraCCH of lira_abstraction
    | LiaCCH of lia_abstraction
    | LraCCH of lra_abstraction

  let alg_of srk = function
    | LiraCCH abs ->
      begin match abs with
      | PolyReccone -> Plt.ConvexHull.cch_lira_lp_pcone srk
      | LiraLPLH eps ->
        begin match eps with
        | None -> Plt.ConvexHull.cch_lira_lplh srk
        | Some epsilon -> Plt.ConvexHull.cch_lira_lplh ~epsilon srk
        end
      | PolyReccone_LPLH eps ->
        begin match eps with
        | None -> Plt.ConvexHull.cch_lira srk
        | Some epsilon -> Plt.ConvexHull.cch_lira ~epsilon srk
        end
      end
    | LiaCCH abs ->
      begin match abs with
        | HullThenProject hull ->
            Plt.ConvexHull.cch_lia_hull_then_project hull srk
        | LiaLPLH -> Plt.ConvexHull.cch_lia srk
      end
    | LraCCH abs ->
      begin match abs with
      | LwMbp -> Plt.ConvexHull.cch_lra srk
      | FullProject -> Plt.ConvexHull.cch_lra_hull_then_project srk
      end

  module S = Syntax.Symbol.Set

  type real_relaxation = NoRelax | JustLraFormula | Realified

  (* Purify flood, mod, div by default *)
  let keep_floor_mod_div = ref false

  let relax_to_real = ref NoRelax

  let pp_alg fmt alg =
    let alg_name =
      match alg with
      | LiraCCH PolyReccone -> "PolyReccone"
      | LiraCCH (LiraLPLH _) -> "Lira-LPLH"
      | LiraCCH (PolyReccone_LPLH _) -> "PolyReccone & LPLH"
      | LiaCCH (HullThenProject `GomoryChvatal) -> "Gomory-Chvatal"
      | LiaCCH (HullThenProject `Normaliz) -> "Normaliz"
      | LiaCCH LiaLPLH -> "Integer-LPLH"
      | LraCCH FullProject -> "Real-projection"
      | LraCCH LwMbp -> "Real-LP"
    in
    let preprocessing =
      match (!relax_to_real, !keep_floor_mod_div) with
      | (Realified, true) -> " of real relaxation (of non-preprocessed formula)"
      | (JustLraFormula, true) -> " of partial real relaxation (of non-preprocessed formula)"
      | (NoRelax, true) -> " (of non-preprocessed formula)"
      | (Realified, false) -> " of real relaxation (of formula)"
      | (JustLraFormula, false) -> " of partial real relaxation (of formula)"
      | (NoRelax, false) -> ""
    in
    Format.fprintf fmt "%s%s" alg_name preprocessing

  let pp_relaxation fmt = function
    | NoRelax -> Format.fprintf fmt "no relax"
    | JustLraFormula -> Format.fprintf fmt "relaxed to LRA formula with types preserved"
    | Realified -> Format.fprintf fmt "real relaxation"

  let retype_quantifier_free srk how phi =
    let retype fml =
      match how with
      | `LiraToLra -> Syntax.retype srk `IntToReal Syntax.Symbol.Map.empty fml
      | `LiraToLia _ -> Syntax.retype srk `RealToInt Syntax.Symbol.Map.empty fml
    in
    let preprocess fml = match how with
      | `LiraToLra -> Syntax.eliminate_floor_mod_div_int srk fml
      | `LiraToLia `LraTerms -> Syntax.eliminate_floor_mod_div srk fml
      | `LiraToLia `LraFormula -> Syntax.eliminate_floor_mod_div_int srk fml
      | `LiraToLia `JustSymbols -> fml
    in
    let processed_phi =
      Syntax.rewrite srk ~down:(nnf_rewriter srk) phi
      |> rewrite srk ~down:(pos_rewriter srk)
      |> preprocess in
    let introduced_symbols = S.diff (symbols processed_phi) (symbols phi) in
    let (retyped_processed, map) = retype processed_phi in
    let remap_symbols s =
      match Symbol.Map.find_opt s map with
      | Some new_sym -> new_sym
      | None -> s
    in
    let introduced_symbols' =
      introduced_symbols |> S.map remap_symbols
    in
    let equivalent = (Symbol.Map.is_empty map) in
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

  let pp_dim fmt dim = Format.fprintf fmt "(dim %d)" dim

  let dd_subset dd1 dd2 =
    BatEnum.for_all
      (fun cnstrnt ->
        DD.implies dd1 cnstrnt)
      (DD.enum_constraints dd2)

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

  let _convex_hull how srk processed_phi terms =
    let man = Polka.manager_alloc_loose () in
    let solver = Abstract.Solver.make srk ~theory:`LIRA processed_phi in
    let local_abs = alg_of srk how ~man (symbols processed_phi) terms in
    Abstract.ClosedConvexHull.abstract_by ~man solver (`LIRA local_abs) terms

  let convex_hull srk how phi =
    let (qf, phi) = Quantifier.normalize srk phi in
    if List.exists (fun (q, _) -> q = `Forall) qf then
      failwith "universal quantification not supported";
    let quantified_symbols = List.map (fun (_, sym) -> sym) qf in
    let original_symbols_to_keep = S.diff (symbols phi) (S.of_list quantified_symbols) in
    let (processed_phi, introduced_symbols, remap) =
      match !relax_to_real with
      | Realified ->
         let (phi', introduced_symbols', map, _) = retype_quantifier_free srk `LiraToLra phi in
         (phi', introduced_symbols', map)
      | JustLraFormula ->
         let phi' = Syntax.eliminate_floor_mod_div_int srk phi in
         let introduced_symbols = S.diff (Syntax.symbols phi') (Syntax.symbols phi) in
         (phi', introduced_symbols, (fun s -> s))
      | NoRelax ->
         if !keep_floor_mod_div then
           (phi, Syntax.Symbol.Set.empty, (fun s -> s))
         else
           let phi' = Syntax.eliminate_floor_mod_div srk phi in
           let introduced_symbols = S.diff (Syntax.symbols phi') (Syntax.symbols phi) in
           (phi', introduced_symbols, (fun s -> s))
    in
    let symbols_to_eliminate =
      S.union introduced_symbols (S.of_list (List.map remap quantified_symbols)) in
    Format.printf "Quantified symbols: %a\n"
      (Format.pp_print_list ~pp_sep:Format.pp_print_space
         (fun fmt (_, sym) -> (Syntax.pp_symbol srk) fmt sym)) qf;
    Format.printf "Introduced symbols: %a\n"
      (Format.pp_print_list ~pp_sep:Format.pp_print_space (Syntax.pp_symbol srk))
      (S.to_list introduced_symbols);

    let symbols = Syntax.symbols processed_phi in
    let symbols_to_keep = S.diff symbols symbols_to_eliminate in
    assert (S.cardinal symbols_to_keep = S.cardinal original_symbols_to_keep);
    let terms =
      List.map (fun sym -> Syntax.mk_const srk (remap sym)) (S.to_list original_symbols_to_keep)
      (* Order matters, and we map using the order of original symbols to allow
         comparison between methods *)
      |> Array.of_list
    in
    let print_input () =
      let (int_symbols, _real_symbols) =
        let is_int sym =
          match Syntax.typ_symbol srk sym with
          | `TyInt -> true
          | _ -> false
        in
        let is_real sym =
          match Syntax.typ_symbol srk sym with
          | `TyReal -> true
          | _ -> false
        in
        (S.filter is_int symbols, S.filter is_real symbols)
      in
      (* Format.printf "Formula before processing: @[%a@]@;"
         (Syntax.Formula.pp srk) phi; *)
      Format.printf "Taking convex hull of formula: @[%a@]@;"
        (Syntax.Formula.pp srk) processed_phi;
      Format.printf "Symbols to keep: @[%a@]@;" pp_symbols symbols_to_keep;
      Format.printf "Symbols to eliminate: @[%a@]@;" pp_symbols symbols_to_eliminate;
      Format.printf "Integer symbols: @[%a@]@;"
        (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
           (fun fmt sym -> Format.fprintf fmt "%s" (Syntax.show_symbol srk sym)))
        (Symbol.Set.to_list int_symbols)
    in
    print_input ();
    let result = _convex_hull how srk processed_phi terms in
    Format.printf "Convex hull:@\n @[<v 0>%a@]@\n"
      (Syntax.Formula.pp srk)
      (formula_of_dd srk (fun dim -> terms.(dim)) result);
    result

  let compare srk test (alg1, relax1) (alg2, relax2) phi =
    Format.printf "Comparing convex hulls computed by %a (%a) and by %a (%a)@\n"
      pp_alg alg1 pp_relaxation relax1 pp_alg alg2 pp_relaxation relax2;

    relax_to_real := relax1;
    let hull1 = convex_hull srk alg1 phi in
    Format.printf "%a hull: @[%a (%a)@]@\n@\n" pp_alg alg1 pp_relaxation relax1
      (DD.pp pp_dim) hull1;

    relax_to_real := relax2;
    let hull2 = convex_hull srk alg2 phi in
    Format.printf "%a hull: @[%a (%a)@]@\n@\n" pp_alg alg2 pp_relaxation relax2 (DD.pp pp_dim) hull2;

    if test hull1 hull2 then
      Format.printf "Result: success"
    else
      if dd_subset hull1 hull2 then
        begin
          relax_to_real := relax1;
          Format.printf "Result: failure (%a (%a) is more precise)"
            pp_alg alg1 pp_relaxation relax1
        end
      else if dd_subset hull2 hull1 then
        begin
          relax_to_real := relax2;
          Format.printf "Result: failure (%a (%a) is more precise)"
            pp_alg alg2 pp_relaxation relax2
        end
      else
        let () = (relax_to_real := relax1) in
        let s1 = Format.asprintf "%a (%a)" pp_alg alg1 pp_relaxation relax1 in
        let () = (relax_to_real := relax2) in
        let s2 = Format.asprintf "%a (%a)" pp_alg alg2 pp_relaxation relax2 in
        Format.printf "Result: failure (%s and %s incomparable)" s1 s2

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
   "Set weak theory solver to use Normaliz's integer hull computation (instead of Gomory-Chvatal");

  ("-generator",
   Arg.Set generator_rep,
   " Print generator representation of convex hull");

  ("-lira-convex-hull-pc"
  , Arg.String
      (fun file ->
        ConvHull.relax_to_real := NoRelax;
        ignore
          (ConvHull.convex_hull srk (ConvHull.LiraCCH PolyReccone)
             (load_formula file));
        Format.printf "Result: success"
      )
  ,
    "Compute the convex hull of an existential formula in LIRA
     using the polyhedral-level-set-and-recession-cone abstraction"
  );

  ("-lira-convex-hull-lplh"
  , Arg.String
      (fun file ->
        ConvHull.relax_to_real := NoRelax;
        ignore
          (ConvHull.convex_hull srk (ConvHull.LiraCCH (LiraLPLH None)) (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in LIRA using local projection
     followed by taking local hull, the latter of which is based on
     'An efficient quantifier elimination procedure for Presburger arithmetic' (ICALP 2024))."
  );

  ("-lira-convex-hull-pc-lplh"
  , Arg.String
      (fun file ->
        ConvHull.relax_to_real := NoRelax;
        ignore (ConvHull.convex_hull srk (ConvHull.LiraCCH (PolyReccone_LPLH None)) (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in LIRA using the join of
     -lira-convex-hull-pc and -lira-convex-hull-lplh"
  );

  ("-lira-convex-hull-real-relaxation-lw"
  , Arg.String
      (fun file ->
        ConvHull.relax_to_real := Realified;
        ignore (ConvHull.convex_hull srk (LraCCH LwMbp) (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in LIRA by first expressing it as an equivalent formula in the signature of LRA using more variables, casting all variables to real, and then doing local projection."
  );

  ("-lira-convex-hull-real-relaxation-fmcad15"
  , Arg.String
      (fun file ->
        ConvHull.relax_to_real := Realified;
        ignore (ConvHull.convex_hull srk (LraCCH FullProject) (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in LIRA by by first expressing it as an equivalent formula in the signature of LRA using more variables, casting all variables to real, and then doing a full projection (FMCAD'15)."
  );

  ("-compare-lira-convex-hull-pc-lplh-vs-pc"
  , Arg.String (fun file ->
        ConvHull.compare srk
          DD.equal (LiraCCH (PolyReccone_LPLH None), NoRelax) (LiraCCH PolyReccone, NoRelax)
          (load_formula file))
  , "Test convex hulls for correctness"
  );

  ("-compare-lira-convex-hull-pc-lplh-vs-lira-lplh"
  , Arg.String (fun file ->
        ConvHull.compare srk
          DD.equal (LiraCCH (PolyReccone_LPLH None), NoRelax) (LiraCCH (LiraLPLH None), NoRelax)
          (load_formula file))
  , "Test convex hulls computed by -lira-convex-hull-pc-lplh with that of -lira-convex-hull-lplh"
  );

  ("-compare-lira-convex-hull-pc-lplh-vs-real-relaxation-lw"
  , Arg.String (fun file ->
        ConvHull.compare srk
          DD.equal (LiraCCH (PolyReccone_LPLH None), NoRelax) (LraCCH LwMbp, Realified)
          (load_formula file))
  , "Compare convex hull of a LIRA formula against that of its real relaxation"
  );

  ("-compare-lira-convex-hull-pc-lplh-vs-lw"
  , Arg.String (fun file ->
        ConvHull.compare srk
          DD.equal
          (LiraCCH (PolyReccone_LPLH None), NoRelax)
          (LraCCH LwMbp, JustLraFormula)
          (load_formula file))
  , "Compare convex hull of a LIRA formula against that of -lra-convex-hull-lw (integer symbols preserved if any, but explicit is_int constraints are ignored)"
  );

  ("-compare-lira-convex-hull-partial-relaxation-vs-full-relaxation"
  , Arg.String (fun file ->
        ConvHull.compare srk DD.equal
          (LraCCH LwMbp, JustLraFormula) (LraCCH LwMbp, Realified)
          (load_formula file))
  , "Compare convex hull of partially relaxed formula using LW against that of its real relaxation"
  );

  ("-lia-convex-hull-lia-lplh"
  , Arg.String
      (fun file ->
        ConvHull.relax_to_real := NoRelax;
        ignore
          (ConvHull.convex_hull srk (LiaCCH LiaLPLH) (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in LIA by local projection followed by taking local hull."
  );

  ("-lia-convex-hull-hull-then-project-gc"
  , Arg.String
      (fun file ->
        ConvHull.relax_to_real := JustLraFormula;
        ignore
          (ConvHull.convex_hull srk (LiaCCH (HullThenProject `GomoryChvatal)) (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in LIA by computing the integer hull
     using iterated Gomory-Chvatal closure and then projecting it. All variables must be of
     integer type for this to be sound."
  );

  ("-lia-convex-hull-hull-then-project-normaliz"
  , Arg.String
      (fun file ->
        ConvHull.relax_to_real := JustLraFormula;
        ignore
          (ConvHull.convex_hull srk (LiaCCH (HullThenProject `Normaliz)) (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in LIA by computing the integer hull
     using Normaliz and then projecting it. All variables should be of integer type for this to be sound."
  );

  ("-compare-lia-convex-hull-lia-lplh-vs-pc-lplh"
  , Arg.String
      (fun file ->
        ConvHull.compare srk DD.equal
          (LiaCCH LiaLPLH, NoRelax)
          (LiraCCH (PolyReccone_LPLH None), NoRelax)
          (load_formula file)
      )
  , "Test convex hulls for correctness"
  );

  ("-compare-lia-convex-hull-lia-lplh-vs-hull-then-proj-gc"
  , Arg.String
      (fun file ->
        ConvHull.compare srk DD.equal
          (LiaCCH LiaLPLH, NoRelax)
          (LiaCCH (HullThenProject `GomoryChvatal), JustLraFormula)
          (load_formula file)
      )
  , "Test convex hulls for correctness"
  );

  ("-lra-convex-hull-lw"
  , Arg.String
      (fun file ->
        ConvHull.relax_to_real := NoRelax;
        ignore (ConvHull.convex_hull srk (LraCCH LwMbp) (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in LRA using Loos-Weispfenning. This retains integrality (type) of variables; use -lira-convex-hull-real-relxation-lw if variables should be cast to real."
  );

  ("-lra-convex-hull-fmcad15"
  , Arg.String
      (fun file ->
        ConvHull.relax_to_real := NoRelax;
        ignore (ConvHull.convex_hull srk (LraCCH FullProject) (load_formula file));
        Format.printf "Result: success")
  , "Compute the convex hull of an existential formula in linear real arithmetic
     using full projection (FMCAD'15)."
  );

  ("-compare-lra-convex-hull-lw-vs-fmcad15"
  , Arg.String
      (fun file ->
        ConvHull.compare srk DD.equal
          (LraCCH LwMbp, NoRelax) (LraCCH FullProject, NoRelax)
          (load_formula file)
      )
  , "Test convex hulls for correctness"
  );

  ("-integralize-smt-file"
  , Arg.String (fun file ->
        let () =
          if not (Filename.check_suffix file ".smt2") then failwith "not an SMT file"
          else ()
        in
        let phi = load_smtlib2 file in
        let (phi', equivalent) =
          try ConvHull.retype_formula srk (`LiraToLia `LraFormula) phi
          with
          | _ -> Format.printf "Fail at file: %s" file;
                 failwith "Failed"
        in
        let suffix = if equivalent then "_equivalent.smt2" else "_integralized.smt2" in
        let outfilename = (Filename.remove_extension file) ^ suffix in
        Format.printf "Writing to file %s@;" outfilename;
        let fmt = Format.formatter_of_out_channel (open_out outfilename) in
        pp_smtlib2 srk fmt phi'
      )
  , "Make a copy of an SMT file with the formula first replaced by an equivalent formula in the signature of LRA with integer-typed variables, and then all real variables are re-declared as integer"
  );

  ("-realify-smt-file"
  , Arg.String (fun file ->
        let () =
          if not (Filename.check_suffix file ".smt2") then failwith "not an SMT file"
          else ()
        in
        let phi = load_smtlib2 file in
        let (phi', equivalent) =
          try ConvHull.retype_formula srk `LiraToLra phi
          with
          | _ -> Format.printf "Fail at file: %s" file;
                 failwith "Failed"
        in
        let suffix = if equivalent then "_equivalent.smt2" else "_realified.smt2" in
        let outfilename = (Filename.remove_extension file) ^ suffix in
        Format.printf "Writing to file %s@;" outfilename;
        let fmt = Format.formatter_of_out_channel (open_out outfilename) in
        pp_smtlib2 srk fmt phi'
      )
  , "Make a copy of an SMT file with the formula first replaced by an equivalent formula in the signature of LRA with integer-typed variables, and then all integer-typed variables are re-declared as real"
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

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

let retype_formula srk fromto phi =
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
    let expanded_phi = Syntax.eliminate_floor_mod_div_int srk phi in
    let introduced_symbols = Symbol.Set.diff (symbols expanded_phi) (symbols phi) in
    let (retyped_expanded, map) = Syntax.retype srk fromto expanded_phi in
    let equivalent = (Symbol.Map.is_empty map) in
    let remap_symbols s =
      match Symbol.Map.find_opt s map with
      | Some new_sym -> new_sym
      | None -> s
    in
    let new_quantified_symbols =
      let retyped_original = List.map (fun (_, sym) -> remap_symbols sym) qf in
      let retyped_introduced = Symbol.Set.map remap_symbols introduced_symbols
                               |> Symbol.Set.to_list
      in
      retyped_original @ retyped_introduced
    in
    ( requantify new_quantified_symbols retyped_expanded
    , equivalent
    , remap_symbols )

module Plt = PolyhedronLatticeTiling

module ConvHull : sig

  val ignore_quantifiers_in_convhull: unit -> unit

  val dd_subset: DD.closed DD.t -> DD.closed DD.t -> bool

  val acceleration_window: int ref

  val convex_hull:
    'a context ->
    [ `Precise of Plt.abstraction_algorithm
    | `NoElimFMDScHKMMZ
    | `RealRelaxation of [`FullProject | `Lw]
    | `ElimFMDLw
    ] ->
    'a formula -> DD.closed DD.t

  val compare:
    'a context ->
    (DD.closed DD.t -> DD.closed DD.t -> bool) ->
    [ `Precise of Plt.abstraction_algorithm
    | `NoElimFMDScHKMMZ
    | `RealRelaxation of [`FullProject | `Lw]
    | `ElimFMDLw
    ] ->
    [ `Precise of Plt.abstraction_algorithm
    | `NoElimFMDScHKMMZ
    | `RealRelaxation of [`FullProject | `Lw]
    | `ElimFMDLw
    ] ->
    'a formula -> unit

end = struct

  module S = Syntax.Symbol.Set

  let ignore_quantifiers = ref false

  let ignore_quantifiers_in_convhull () = ignore_quantifiers := true

  let pp_dim fmt dim = Format.fprintf fmt "(dim %d)" dim

  let dd_subset dd1 dd2 =
    BatEnum.for_all
      (fun cnstrnt ->
        DD.implies dd1 cnstrnt)
      (DD.enum_constraints dd2)

  let elim_quantifiers quantifiers symbols =
    S.filter
      (fun s -> not (List.exists (fun (_, elim) -> s = elim) quantifiers))
      symbols

  let pp_symbols fmt set =
    Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "@\n")
      (fun fmt sym ->
        Format.fprintf fmt "%a: %a"
          (Syntax.pp_symbol srk) sym pp_typ (typ_symbol srk sym))
      fmt (S.to_list set)

  let acceleration_window = ref 1

  (*
  let pp_alg fmt = function
    | `SubspaceCone -> Format.fprintf fmt "SubspaceCone"
    | `SubspaceConeAccelerated `DiversifyInOriginal ->
       Format.fprintf fmt
         "SubspaceConeAccelerated (using previous %d models in the PLT as a hint)"
         !acceleration_window
    | `SubspaceConeAccelerated `DiversifyInDD ->
       Format.fprintf fmt
         "SubspaceConeAccelerated (using vertices of LW-Cooper projection as a hint)"
    | `SubspaceConeAccelerated `DiversifyInBoth ->
       Format.fprintf fmt
         "SubspaceConeAccelerated (using previous %d models and the vertices of LW-Cooper projection as a hint)" !acceleration_window
    | `SubspaceConePrecondAccelerate -> Format.fprintf fmt "SubspaceConePrecondAccelerated"
    | `IntFrac -> Format.fprintf fmt "IntFrac"
    | `IntFracAccelerated ->
       Format.fprintf fmt "IntFracAccelerated(window=%d)" !acceleration_window
    | `LwCooper `IntRealHullAfterProjection ->
       Format.fprintf fmt "LW + Cooper with mixed hull after projection"
    | `LwCooper `IntHullAfterProjection ->
       Format.fprintf fmt "LW + Cooper with integer hull after projection"
    | `LwCooper `NoIntHullAfterProjection ->
       Format.fprintf fmt "LW + Cooper"
    | `Lw ->
       Format.fprintf fmt
         "LW only (ignore integrality constraints on all symbols when projecting)"
    | `GcThenElim ->
       Format.fprintf fmt
         "Compute integer hull using Gomory-Chvatal closure and DD projection
          directly onto free symbols (i.e., eliminate existentially quantified symbols)"
    | `GcImplicantThenProjectTerms ->
       Format.fprintf fmt
         "Compute integer hull using Gomory-Chvatal closure on each implicant and DD projection
          onto term dimensions (with each term being a free symbol)"
    | `NormalizThenElim ->
       Format.fprintf fmt "Compute integer hull using Normaliz and DD projection"
    | `RunOnlyForPureInt ->
       Format.fprintf fmt "SubspaceConeAccelerated (running on pure integer tasks only)"
   *)

  let pp_alg fmt = function
    | `Precise how ->
       begin match how with
       | Plt.SubspaceCone `Standard -> Format.fprintf fmt "SubspaceCone"
       | Plt.SubspaceCone `WithHKMMZCone ->
          Format.fprintf fmt
            "SubspaceCone joined with the polyhedron of far lattice points"
       | Plt.IntFrac `Standard ->
          Format.fprintf fmt "IntFrac with lattice hull underapproximated using HKMMZCone"
       | Plt.LwCooperHKMMZCone ->
          Format.fprintf fmt "%s"
            (String.concat " "
               [ "Loos-Weispfenning model-based projection for real dimensions +"
               ; "Cooper model-based projection for dimensions appearing in Int constraints +"
               ; "convexify projected PLT using HKMMZ" ])
       | Plt.ProjectImplicant (`AssumeReal `FullProject) ->
          Format.fprintf fmt "FMCAD'15"
       | Plt.ProjectImplicant (`AssumeReal `Lw) ->
          Format.fprintf fmt "Loos-Weispfenning model-based projection + convexify"
       | Plt.ProjectImplicant (`AssumeInt (`HullThenProject `GomoryChvatal)) ->
          Format.fprintf fmt
            "Integer hull of each implicant using Gomory-Chvatal closure followed by DD projection"
       | Plt.ProjectImplicant (`AssumeInt (`HullThenProject `Normaliz)) ->
          Format.fprintf fmt
            "Integer hull of each implicant using Normaliz followed by DD projection"
       | Plt.ProjectImplicant (`AssumeInt (`ProjectThenHull `GomoryChvatal)) ->
          Format.fprintf fmt
            "Cooper's MBP of each implicant followed by integer hull using Gomory-Chvatal closure"
       | Plt.ProjectImplicant (`AssumeInt (`ProjectThenHull `Normaliz)) ->
          Format.fprintf fmt
            "Cooper's MBP of each implicant followed by integer hull using Normaliz"
       end
    | `RealRelaxation `FullProject ->
       Format.fprintf fmt
         "Desugar LIA terms and Ints into LRA, drop integrality constraints, and compute the convex hull by doing a full projection on each implicant (FMCAD'15)"
    | `NoElimFMDScHKMMZ ->
       Format.fprintf fmt "SubspaceCone with HKMMZ without elimination of floor-mod-div terms"
    | `RealRelaxation `Lw ->
       Format.fprintf fmt
         "Desugar LIA terms and Ints into LRA, drop integrality constraints, and compute the convex hull by doing Loos-Weispfenning model-based projection on each implicant and convexifying"
    | `ElimFMDLw ->
       Format.fprintf fmt
         "Desugar LIA terms and Ints, KEEP integrality constraints in SMT solver, and compute the convex hull by doing Loos-Weispfenning model-based projection on each implicant and convexifying"

  let convex_hull srk how phi =
    let (qf, phi) = Quantifier.normalize srk phi in
    if List.exists (fun (q, _) -> q = `Forall) qf then
      failwith "universal quantification not supported";
    let symbols = Syntax.symbols phi in
    let symbols_to_keep = elim_quantifiers qf symbols in
    let terms =
      symbols_to_keep
      |> (fun set -> S.fold (fun sym terms -> mk_const srk sym :: terms) set [])
      |> List.rev
      |> Array.of_list
    in

    (* Normalize formula to be in LIRA(X), which requires formulas to be in NNF
       and free of floor, mod, div.
     *)
    let phi =
      begin match how with
      | `NoElimFMDScHKMMZ -> phi
      | _ ->
         Syntax.rewrite srk ~down:(nnf_rewriter srk) phi
         |> rewrite srk ~down:(pos_rewriter srk)
         |> Syntax.eliminate_floor_mod_div srk
      end
    in
    let symbols = Syntax.symbols phi in

    let print_input () =
      let symbols_to_eliminate =
        S.filter (fun sym -> not (S.mem sym symbols_to_keep)) symbols
      in
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
        let symbols = Syntax.symbols phi in
        (S.filter is_int symbols, S.filter is_real symbols)
      in
      Format.printf "Taking convex hull of formula: @[%a@]@;"
        (Syntax.Formula.pp srk) phi;
      Format.printf "Symbols to keep: @[%a@]@;" pp_symbols symbols_to_keep;
      Format.printf "Symbols to eliminate: @[%a@]@;" pp_symbols symbols_to_eliminate;
      Format.printf "Integer symbols: @[%a@]@;"
        (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
           (fun fmt sym -> Format.fprintf fmt "%s" (Syntax.show_symbol srk sym)))
        (Symbol.Set.to_list int_symbols)
    in
    print_input ();
    let result = match how with
      | `Precise how ->
         Plt.convex_hull how srk phi terms
      | `NoElimFMDScHKMMZ ->
         Plt.convex_hull (Plt.SubspaceCone `WithHKMMZCone) srk phi terms
      | `RealRelaxation how -> Plt.convex_hull_of_real_relaxation how srk phi terms
      | `ElimFMDLw ->
         let expanded_phi = Syntax.eliminate_floor_mod_div_int srk phi in
         Plt.convex_hull (ProjectImplicant (`AssumeReal `Lw)) srk expanded_phi terms
    in
    Format.printf "Convex hull:@\n @[<v 0>%a@]@\n"
      (Syntax.Formula.pp srk)
      (Plt.formula_of_dd srk (fun dim -> terms.(dim)) result);
    result

  let compare srk test alg1 alg2 phi =
    Format.printf "Comparing convex hulls computed by %a and by %a@\n"
      pp_alg alg1 pp_alg alg2;
    let hull1 = convex_hull srk alg1 phi in
    let () =
      Format.printf "%a hull: @[%a@]@\n@\n" pp_alg alg1 (DD.pp pp_dim) hull1 in
    let hull2 = convex_hull srk alg2 phi in
    let () =
      Format.printf "%a hull: @[%a@]@\n@\n" pp_alg alg2 (DD.pp pp_dim) hull2 in
    if test hull1 hull2 then
      Format.printf "Result: success"
    else
      if dd_subset hull1 hull2 then
        Format.printf "Result: failure (%a is more precise)"
          pp_alg alg1
      else if dd_subset hull2 hull1 then
        Format.printf "Result: failure (%a is more precise)"
          pp_alg alg2
      else
        Format.printf "Result: failure (%a and %a incomparable)"
          pp_alg alg1 pp_alg alg2

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

  ("-no-projection",
   Arg.Unit (fun () -> ConvHull.ignore_quantifiers_in_convhull ()),
   "Ignore existential quantifiers when computing convex hull"
  );

  ("-lira-convex-hull-sc"
  , Arg.String
      (fun file ->
        ignore
          (ConvHull.convex_hull srk (`Precise (SubspaceCone `Standard))
             (load_formula file));
        Format.printf "Result: success"
      )
  ,
    "Compute the convex hull of an existential formula in linear integer-real arithmetic
     using the subspace-and-cone abstraction"
  );

  (*
  ("-lira-acceleration-window"
  , Arg.Int (fun n -> Format.printf "Setting window size to %d" n;
                      ConvHull.acceleration_window := n)
  , "Set the window size of models that accelerated convex hull methods use"
  );

  ("-lira-convex-hull-sc-accelerated"
  , Arg.String
      (fun file ->
        ignore (ConvHull.convex_hull srk
                  (`SubspaceConeAccelerated `DiversifyInOriginal)
                  (load_formula file));
        Format.printf "Result: success"
      )
  ,
    "Compute the convex hull of an existential formula in linear integer-real arithmetic
     using the subspace-and-cone abstraction accelerated by using the previous model
     as a hint."
  );

  ("-lira-convex-hull-sc-diversify-in-both"
  , Arg.String
      (fun file ->
        ignore (ConvHull.convex_hull srk
                  (`SubspaceConeAccelerated `DiversifyInBoth)
                  (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in linear integer-real arithmetic
     using the subspace-and-cone abstraction accelerated by using the previous model
     and vertices of the LW-Cooper projection as a hint."
  );

  ("-lira-convex-hull-sc-precond-accelerate"
  , Arg.String
      (fun file ->
          ignore (ConvHull.convex_hull srk `SubspaceConePrecondAccelerate (load_formula file));
          Format.printf "Result: success"
      )
  ,
    "Compute the convex hull of an existential formula in linear integer-real arithmetic
     using the subspace-and-cone abstraction"
  );
   *)

  ("-lira-convex-hull-intfrac"
  , Arg.String
      (fun file ->
        ignore (ConvHull.convex_hull srk (`Precise (IntFrac `Standard))
                  (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in linear integer-real arithmetic
     using integer-fractional polyhedra-lattice-tilings"
  );

  (*
  ("-lira-convex-hull-intfrac-accelerated"
  , Arg.String
      (fun file ->
        ignore (ConvHull.convex_hull srk `IntFracAccelerated (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in linear integer-real arithmetic
     using integer-fractional polyhedra-lattice-tilings"
  );
   *)

  ("-lira-convex-hull-lwcooper-hkmmzcone"
  , Arg.String
      (fun file ->
        ignore
          (ConvHull.convex_hull srk (`Precise LwCooperHKMMZCone) (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in linear integer-real
     arithmetic by model-based projection using Loos-Weispfenning elimination
     for variables not occurring in integrality constraints and
     (sound) Cooper model-based projection for variables that occur in
     integrality constraints, and taking the convex hull of lattice points
     that are far away using the algorithm from
     'An efficient quantifier elimination procedure for Presburger arithmetic' (ICALP 2024))."
  );

  ("-lira-convex-hull-sc-hkmmzcone"
  , Arg.String
      (fun file ->
        ignore (ConvHull.convex_hull srk
                  (`Precise (SubspaceCone `WithHKMMZCone))
                  (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in linear integer-real arithmetic
     using -lira-convex-hull-sc and -lira-convex-hull-lwcooper-hkmmzcone"
  );

  ("-lira-convex-hull-real-relaxation-lw"
  , Arg.String
      (fun file ->
        ignore (ConvHull.convex_hull srk (`RealRelaxation `Lw) (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in linear integer-real arithmetic
     by desugaring LIA terms and Ints into LRA, dropping integrality constraints
     (integer-typed variables are replaced with real-typed ones), and projecting each
     implicant using Loos-Weispfening model-based projection"
  );

  ("-lira-convex-hull-real-relaxation-fmcad15"
  , Arg.String
      (fun file ->
        ignore (ConvHull.convex_hull srk (`RealRelaxation `FullProject) (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in linear integer-real arithmetic
     by desugaring LIA terms and Ints into LRA, dropping integrality constraints
     (integer-typed variables are replaced with real-typed ones), and projecting each
     implicant using Loos-Weispfening model-based projection"
  );

  ("-lira-convex-hull-elimfmd-lw"
  , Arg.String
      (fun file ->
        ignore (ConvHull.convex_hull srk `ElimFMDLw (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in linear integer-real arithmetic
     by desugaring LIA terms and Ints into LRA, KEEPING integrality constraints in the
     SMT solver, and projecting each implicant using Loos-Weispfening model-based projection"
  );

  ("-compare-convex-hull-sc-vs-sc-hkmmzcone"
  , Arg.String (fun file ->
        ConvHull.compare srk
          DD.equal (`Precise (SubspaceCone `Standard)) (`Precise (SubspaceCone `WithHKMMZCone))
          (load_formula file))
  , "Test convex hulls for correctness"
  );

  ("-compare-convex-hull-sc-hkmmzcone-vs-lwcooper-hkmmzcone"
  , Arg.String (fun file ->
        ConvHull.compare srk
          DD.equal (`Precise (SubspaceCone `WithHKMMZCone)) (`Precise LwCooperHKMMZCone)
          (load_formula file))
  , "Test convex hulls computed by -lira-convex-hull-sc-hkmmzcone with that of -lira-convex-hull-lwcooper-hkmmzcone"
  );

  ("-compare-convex-hull-sc-hkmmzcone-vs-intfrac"
  , Arg.String (fun file ->
        ConvHull.compare srk
          DD.equal (`Precise (SubspaceCone `WithHKMMZCone)) (`Precise (IntFrac `Standard))
          (load_formula file))
  , "Test convex hulls computed by -lira-convex-hull-sc-hkmmzcone with that of -lira-convex-hull-intfrac"
  );

  ("-compare-convex-hull-sc-hkmmzcone-vs-noelimfmd-sc-hkmmzcone"
  , Arg.String (fun file ->
        ConvHull.compare srk
          DD.equal (`Precise (SubspaceCone `WithHKMMZCone)) (`NoElimFMDScHKMMZ)
          (load_formula file))
  , "Compare convex hulls computed by -lira-convex-hull-sc-hkmmzcone with the same algorithm without floor-mod-div elimination"
  );

  ("-compare-convex-hull-sc-hkmmzcone-vs-real-relaxation-lw"
  , Arg.String (fun file ->
        ConvHull.compare srk
          DD.equal (`Precise (SubspaceCone `WithHKMMZCone)) (`RealRelaxation `Lw)
          (load_formula file))
  , "Compare convex hull of a LIRA formula against that of its real relaxation"
  );

  ("-compare-convex-hull-sc-hkmmzcone-vs-lw"
  , Arg.String (fun file ->
        ConvHull.compare srk
          DD.equal
          (`Precise (SubspaceCone `WithHKMMZCone))
          (`Precise (ProjectImplicant (`AssumeReal `Lw)))
          (load_formula file))
  , "Compare convex hull of a LIRA formula against that of -lra-convex-hull-lw"
  );

  ("-compare-convex-hull-sc-hkmmzcone-vs-elimfmd-lw"
  , Arg.String (fun file ->
        ConvHull.compare srk
          DD.equal
          (`Precise (SubspaceCone `WithHKMMZCone))
          `ElimFMDLw
          (load_formula file))
  , "Compare convex hull of a LIRA formula against that of -lira-convex-hull-elimfmd-lw"
  );

  ("-compare-convex-hull-sc-hkmmzcone-vs-real-relaxation-lw"
  , Arg.String (fun file ->
        ConvHull.compare srk
          DD.equal
          (`Precise (SubspaceCone `WithHKMMZCone))
          (`RealRelaxation `Lw)
          (load_formula file))
  , "Compare convex hull of a LIRA formula against that of -lira-convex-hull-real-relaxation-lw"
  );

  ("-compare-convex-hull-elimfmd-lw-vs-real-relaxation-lw"
  , Arg.String (fun file ->
        ConvHull.compare srk DD.equal `ElimFMDLw (`RealRelaxation `Lw) (load_formula file))
  , "Compare convex hull of partially relaxed formula using LW against that of its real relaxation"
  );

  ("-lia-convex-hull-by-hull-then-project-gc"
  , Arg.String
      (fun file ->
        ignore
          (ConvHull.convex_hull srk
             (`Precise (ProjectImplicant (`AssumeInt (`HullThenProject `GomoryChvatal))))
             (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in linear integer arithmetic
     with only trivial integrality constraints (i.e., positive Int(x) for variables x only),
     by computing the integer hull using iterated Gomory-Chvatal closure and then projecting it.
     This is sound for formulas that conform to the output of -integralize-smt-file."
  );

  ("-lia-convex-hull-by-hull-then-project-normaliz"
  , Arg.String
      (fun file ->
        ignore (ConvHull.convex_hull srk
                  (`Precise (ProjectImplicant (`AssumeInt (`HullThenProject `Normaliz))))
                  (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in linear integer arithmetic
     with only trivial integrality constraints (i.e., positive Int(x) for variables x only),
     by computing the integer hull using Normaliz and then projecting it.
     This is sound for formulas that conform to the output of -integralize-smt-file."
  );

  ("-lia-convex-hull-by-project-then-hull-gc"
  , Arg.String
      (fun file ->
        ignore (ConvHull.convex_hull srk
                  (`Precise (ProjectImplicant (`AssumeInt (`ProjectThenHull `GomoryChvatal))))
                  (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in linear integer arithmetic
     by Cooper model-based projection and then taking the integer hull using iterated Gomory-Chvatal closure.
     This is sound for formulas that conform to the output of -integralize-smt-file."
  );

  ("-lia-convex-hull-by-project-then-hull-normaliz"
  , Arg.String
      (fun file ->
        ignore (ConvHull.convex_hull srk
                  (`Precise (ProjectImplicant (`AssumeInt (`ProjectThenHull `Normaliz))))
                  (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in linear integer arithmetic
     by Cooper model-based projection and then taking the integer hull using Normaliz.
     This is sound for formulas that conform to the output of -integralize-smt-file."
  );

  ("-compare-lia-convex-hull-hull-then-proj-gc-vs-proj-then-hull-gc"
  , Arg.String
      (fun file ->
        ConvHull.compare srk DD.equal
          (`Precise (ProjectImplicant (`AssumeInt (`HullThenProject `GomoryChvatal))))
          (`Precise (ProjectImplicant (`AssumeInt (`ProjectThenHull `GomoryChvatal))))
          (load_formula file)
      )
  , "Test convex hulls for correctness"
  );

  ("-compare-lia-convex-hull-sc-hkmmzcone-vs-proj-then-hull-gc"
  , Arg.String
      (fun file ->
        ConvHull.compare srk DD.equal
          (`Precise (SubspaceCone `WithHKMMZCone))
          (`Precise (ProjectImplicant (`AssumeInt (`ProjectThenHull `GomoryChvatal))))
          (load_formula file)
      )
  , "Test convex hulls for correctness"
  );

  ("-compare-lia-convex-hull-sc-hkmmzcone-vs-lwcooper-hkmmzcone"
  , Arg.String
      (fun file ->
        ConvHull.compare srk DD.equal
          (`Precise (SubspaceCone `WithHKMMZCone))
          (`Precise LwCooperHKMMZCone)
          (load_formula file)
      )
  , "Test convex hulls for correctness"
  );

  ("-lra-convex-hull-lw"
  , Arg.String
      (fun file ->
        ignore (ConvHull.convex_hull srk (`Precise (ProjectImplicant (`AssumeReal `Lw)))
                  (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in linear real arithmetic
     using Loos-Weispfenning."
  );

  ("-lra-convex-hull-fmcad15"
  , Arg.String
      (fun file ->
        ignore (ConvHull.convex_hull srk (`Precise (ProjectImplicant (`AssumeReal `FullProject)))
                  (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in linear real arithmetic
     using full projection (FMCAD'15)."
  );

  ("-compare-lra-convex-hull-fmcad15-vs-lw"
  , Arg.String
      (fun file ->
        ConvHull.compare srk DD.equal
          (`Precise (ProjectImplicant (`AssumeReal `FullProject)))
          (`Precise (ProjectImplicant (`AssumeReal `Lw)))
          (load_formula file)
      )
  , "Test convex hulls for correctness"
  );

  ("-compare-lra-convex-hull-sc-hkmmzcone-vs-lw"
  , Arg.String
      (fun file ->
        ConvHull.compare srk DD.equal
          (`Precise (SubspaceCone `WithHKMMZCone))
          (`Precise (ProjectImplicant (`AssumeReal `Lw)))
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
        let (phi', equivalent, _) =
          try retype_formula srk `RealToInt phi
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
  , "Make a copy of an SMT file with the formula first de-sugared into LRA + integer-typed variables,
     and then all real variables are re-declared as integer"
  );

  ("-realify-smt-file"
  , Arg.String (fun file ->
        let () =
          if not (Filename.check_suffix file ".smt2") then failwith "not an SMT file"
          else ()
        in
        let phi = load_smtlib2 file in
        let (phi', equivalent, _) =
          try retype_formula srk `IntToReal phi
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
  , "Make a copy of an SMT file with the formula first de-sugared into LRA + integer-typed variables,
     and then all integer-typed variables are re-declared as real"
  );

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

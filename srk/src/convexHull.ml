open Syntax
open BatPervasives

include Log.Make (struct let name = "srk.convexHull" end)

module Solver = Abstract.Solver
module V = Linear.QQVector
module LM = Linear.MakeLinearMap(QQ)(SrkUtil.Int)(V)(V)
module QQXs = Polynomial.QQXs
module I = Polynomial.Rewrite
module Plt = PolyhedronLatticeTiling

type t = DD.closed DD.t

let nb_hulls = ref 0
let dump_hull = ref false
let dump_hull_prefix = ref ""

let lira_retype_as_real = ref false
let purify_formula = ref true

let dump_hull_obligations srk phi terms =
  if !dump_hull then begin
      let query =
        List.fold_left (fun definitions term ->
            let s = mk_symbol srk ?name:(Some "term_to_project_onto") `TyReal
            in
            (Syntax.mk_eq srk (Syntax.mk_const srk s) term :: definitions)
          )
          []
          (Array.to_list terms)
        |> Syntax.mk_and srk
        |> (fun phi' -> Syntax.mk_and srk [phi ; phi'])
      in
      let term_symbols =
        Array.fold_left (fun acc_symbols term -> Symbol.Set.union acc_symbols (symbols term))
          Symbol.Set.empty terms
      in
      let query =
        Symbol.Set.fold (fun s psi -> Syntax.mk_exists_const srk s psi)
          (Symbol.Set.union term_symbols (symbols phi))
          query
      in
      let filename =
        Format.sprintf "%s-hull-%d.smt2" (!dump_hull_prefix) (!nb_hulls)
      in
      let chan = Stdlib.open_out filename in
      let formatter = Format.formatter_of_out_channel chan in
      logf ~level:`always "Writing convex hull query to %s" filename;
      Syntax.pp_smtlib2 srk formatter query;
      Format.pp_print_newline formatter ();
      Stdlib.close_out chan;
      incr nb_hulls
    end;
  ()

let of_model_lirr solver man terms =
  let srk = Solver.get_context solver in
  let poly_terms = Array.map (QQXs.of_term srk) terms in
  let dim = Array.length terms in
  function
  | `LIRA _ -> assert false
  | `LIRR m ->
    let cone = Lirr.Model.nonnegative_cone m in
    let map_cone = PolynomialCone.inverse_image cone poly_terms in
    let constraints = BatEnum.empty () in
    I.generators (PolynomialCone.get_ideal map_cone)
    |> List.iter (fun p ->
        match QQXs.vec_of p with
        | Some vec -> BatEnum.push constraints (`Zero, vec)
        | None -> ());
    PolynomialCone.get_cone_generators map_cone
    |> List.iter (fun p ->
        match QQXs.vec_of p with
        | Some vec -> BatEnum.push constraints (`Nonneg, vec)
        | None -> ());
    DD.of_constraints_closed ~man dim constraints

let conv_hull ?(man=Polka.manager_alloc_loose ()) srk phi terms =
  dump_hull_obligations srk phi terms;
  match !lira_retype_as_real with
  | false ->
     let phi' =
       if !purify_formula then Syntax.eliminate_floor_mod_div srk phi else phi
     in
     Plt.convex_hull (LiraCCH (PolyReccone_LPLH None)) ~man srk phi' terms
  | true ->
     let phi' =
       if !purify_formula then Syntax.eliminate_floor_mod_div_int srk phi else phi
     in
     let (relaxed_phi, realified_terms, _) = Plt.realify_formula_and_terms srk phi' terms in
     Plt.convex_hull (LraCCH LwMbp) ~man srk relaxed_phi realified_terms

let abstract solver ?(man=Polka.manager_alloc_loose ()) ?(bottom=None) terms =
  let srk = Solver.get_context solver in
  let phi = Solver.get_formula solver in
  dump_hull_obligations srk phi terms;
  match Solver.get_theory solver with
  | `LIRR ->
     let join = DD.join in
     let dim = Array.length terms in
     let top = DD.of_constraints_closed ~man dim (BatEnum.empty ()) in
     let bottom = match bottom with
       | Some bot -> bot
       | None ->
          let inconsistent = (* 0 = 1 *)
            BatEnum.singleton (`Zero, V.of_term QQ.one Linear.const_dim)
          in
          DD.of_constraints_closed ~man dim inconsistent
     in
     let term_of_dim i =
       if i == Linear.const_dim then mk_one srk else terms.(i)
     in
     let formula_of prop =
       DD.enum_constraints_closed prop
       /@ (fun (kind, v) ->
         let t = Linear.term_of_vec srk term_of_dim v in
         match kind with
         | `Zero -> mk_eq srk (mk_zero srk) t
         | `Nonneg -> mk_leq srk (mk_zero srk) t)
       |> BatList.of_enum
       |> mk_and srk
     in
     let of_model = of_model_lirr solver man terms in
     let domain =
       Abstract.{ join; top; of_model; bottom; formula_of }
     in
     Solver.abstract solver domain
  | `LIRA ->
     begin match !lira_retype_as_real, !purify_formula with
     | (false, false) ->
        Plt.abstract (LiraCCH (PolyReccone_LPLH None)) ~man ~bottom solver terms
     | (_, _) ->
        conv_hull ~man (Solver.get_context solver) phi terms
     end

(** Low-level interface that assumes formula is in the right form for Plt.convex_hull:
    and for LRA relaxation, this means the formula is in LRA with no LIA terms like
    [mod], no [Int] literals, and all variables are of type [`TyReal].
 *)
let of_model_lira solver man terms model =
  Plt.convex_hull_from_lira_model (LiraCCH (PolyReccone_LPLH None)) ~man
    solver terms model

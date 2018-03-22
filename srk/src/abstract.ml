open Syntax
open Linear
open BatPervasives
open Polyhedron

include Log.Make(struct let name = "srk.abstract" end)

module V = Linear.QQVector
module CS = CoordinateSystem

let opt_abstract_limit = ref (-1)

(* Counter-example based extraction of the affine hull of a formula.  This
   works by repeatedly posing new (linearly independent) equations; each
   equation is either implied by the formula (and gets added to the affine
   hull) or there is a counter-example point which shows that it is not.
   Counter-example points are collecting in a system of linear equations where
   the variables are the coefficients of candidate equations. *)
let affine_hull srk phi constants =
  let solver = Smt.mk_solver srk in
  Smt.Solver.add solver [phi];
  let next_row =
    let n = ref (-1) in
    fun () -> incr n; (!n)
  in
  let vec_one = QQVector.of_term QQ.one Linear.const_dim in
  let rec go equalities mat = function
    | [] -> equalities
    | (k::ks) ->
      let dim = dim_of_sym k in
      let row_num = next_row () in
      (* Find a candidate equation which is satisfied by all previously
         sampled points, and where the coefficient of k is 1 *)
      let mat' = QQMatrix.add_row row_num (QQVector.of_term QQ.one dim) mat in
      match Linear.solve mat' (QQVector.of_term QQ.one row_num) with
      | None -> go equalities mat ks
      | Some candidate ->
        Smt.Solver.push solver;
        let candidate_term =
          QQVector.enum candidate
          /@ (fun (coeff, dim) ->
              match sym_of_dim dim with
              | Some const -> mk_mul srk [mk_real srk coeff; mk_const srk const]
              | None -> mk_real srk coeff)
          |> BatList.of_enum
          |> mk_add srk
        in
        Smt.Solver.add solver [
          mk_not srk (mk_eq srk candidate_term (mk_real srk QQ.zero))
        ];
        match Smt.Solver.get_concrete_model solver constants with
        | `Unknown -> (* give up; return the equalities we have so far *)
          logf ~level:`warn
            "Affine hull timed out (%d equations)"
            (List.length equalities);
          equalities
        | `Unsat -> (* candidate equality is implied by phi *)
          Smt.Solver.pop solver 1;
          (* We never choose the same candidate equation again, because the
             system of equations mat' x = 0 implies that the coefficient of k
             is zero *)
          go (candidate_term::equalities) mat' ks
        | `Sat point -> (* candidate equality is not implied by phi *)
          Smt.Solver.pop solver 1;
          let point_row =
            List.fold_left (fun row k ->
                QQVector.add_term
                  (Interpretation.real point k)
                  (dim_of_sym k)
                  row)
              vec_one
              constants
          in
          let mat' = QQMatrix.add_row row_num point_row mat in
          (* We never choose the same candidate equation again, because the
             only solutions to the system of equations mat' x = 0 are
             equations which are satisfied by the sampled point *)
          go equalities mat' (k::ks)
  in
  go [] QQMatrix.zero constants

let boxify srk phi terms =
  let mk_box t ivl =
    let lower =
      match Interval.lower ivl with
      | Some lo -> [mk_leq srk (mk_real srk lo) t]
      | None -> []
    in
    let upper =
      match Interval.upper ivl with
      | Some hi -> [mk_leq srk t (mk_real srk hi)]
      | None -> []
    in
    lower@upper
  in
  match SrkZ3.optimize_box srk phi terms with
  | `Sat intervals ->
    mk_and srk (List.concat (List.map2 mk_box terms intervals))
  | `Unsat -> mk_false srk
  | `Unknown -> assert false

let abstract ?exists:(p=fun x -> true) srk man phi =
  let solver = Smt.mk_solver srk in
  let phi_symbols = symbols phi in
  let symbol_list = Symbol.Set.elements phi_symbols in
  let env_proj = SrkApron.Env.of_set srk (Symbol.Set.filter p phi_symbols) in
  let cs = CoordinateSystem.mk_empty srk in

  let projected_coordinates =
    Symbol.Set.fold (fun sym project ->
        if p sym then
          project
        else
          (CS.cs_term_id ~admit:true cs (`App (sym, [])))::project)
      phi_symbols
      []
  in

  let disjuncts = ref 0 in
  let rec go prop =
    Smt.Solver.push solver;
    Smt.Solver.add solver [mk_not srk (SrkApron.formula_of_property prop)];
    let result =
      Log.time "lazy_dnf/sat" (Smt.Solver.get_concrete_model solver) symbol_list
    in
    match result with
    | `Unsat ->
      Smt.Solver.pop solver 1;
      prop
    | `Unknown ->
      begin
        logf ~level:`warn "abstraction timed out (%d disjuncts); returning top"
          (!disjuncts);
        Smt.Solver.pop solver 1;
        SrkApron.top man env_proj
      end
    | `Sat interp -> begin
        Smt.Solver.pop solver 1;
        incr disjuncts;
        logf "[%d] abstract lazy_dnf" (!disjuncts);
        if (!disjuncts) = (!opt_abstract_limit) then begin
          logf ~level:`warn "Met symbolic abstraction limit; returning top";
          SrkApron.top man env_proj
        end else begin
          let disjunct =
            match Interpretation.select_implicant interp phi with
            | Some d -> Polyhedron.of_implicant ~admit:true cs d
            | None -> assert false
          in
          let valuation =
            let table : QQ.t array =
              Array.init (CS.dim cs) (fun i ->
                  Interpretation.evaluate_term
                    interp
                    (CS.term_of_coordinate cs i))
            in
            fun i -> table.(i)
          in
          let projected_disjunct =
            Polyhedron.local_project valuation projected_coordinates disjunct
            |> Polyhedron.to_apron cs env_proj man
          in
          go (SrkApron.join prop projected_disjunct)
        end
      end
  in
  Smt.Solver.add solver [phi];
  Log.time "Abstraction" go (SrkApron.bottom man env_proj)

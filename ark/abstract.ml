open Syntax
open Linear
open BatPervasives
open Apak
open Polyhedron

include Log.Make(struct let name = "ark.abstract" end)

module V = Linear.QQVector
module VS = Putil.Set.Make(Linear.QQVector)
module VM = Putil.Map.Make(Linear.QQVector)

let opt_abstract_limit = ref (-1)

(* Counter-example based extraction of the affine hull of a formula.  This
   works by repeatedly posing new (linearly independent) equations; each
   equation is either implied by the formula (and gets added to the affine
   hull) or there is a counter-example point which shows that it is not.
   Counter-example points are collecting in a system of linear equations where
   the variables are the coefficients of candidate equations. *)
let affine_hull ark phi constants =
  let solver = Smt.mk_solver ark in
  solver#add [phi];
  let next_row =
    let n = ref (-1) in
    fun () -> incr n; (!n)
  in
  let vec_one = QQVector.of_term QQ.one 0 in
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
        solver#push ();
        let candidate_term =
          QQVector.enum candidate
          /@ (fun (coeff, dim) ->
              match sym_of_dim dim with
              | Some const -> mk_mul ark [mk_real ark coeff; mk_const ark const]
              | None -> mk_real ark coeff)
          |> BatList.of_enum
          |> mk_add ark
        in
        solver#add [
          mk_not ark (mk_eq ark candidate_term (mk_real ark QQ.zero))
        ];
        match solver#get_model () with
        | `Unknown -> (* give up; return the equalities we have so far *)
          logf ~level:`warn
            "Affine hull timed out (%d equations)"
            (List.length equalities);
          equalities
        | `Unsat -> (* candidate equality is implied by phi *)
          solver#pop 1;
          (* We never choose the same candidate equation again, because the
             system of equations mat' x = 0 implies that the coefficient of k is
             zero *)
          go (candidate_term::equalities) mat' ks
        | `Sat point -> (* candidate equality is not implied by phi *)
          solver#pop 1;
          let point_row =
            List.fold_left (fun row k ->
                QQVector.add_term
                  (point#eval_real (mk_const ark k))
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

let boxify ark phi terms =
  let mk_box t ivl =
    let lower =
      match Interval.lower ivl with
      | Some lo -> [mk_leq ark (mk_real ark lo) t]
      | None -> []
    in
    let upper =
      match Interval.upper ivl with
      | Some hi -> [mk_leq ark t (mk_real ark hi)]
      | None -> []
    in
    lower@upper
  in
  match ArkZ3.optimize_box ark phi terms with
  | `Sat intervals ->
    mk_and ark (List.concat (List.map2 mk_box terms intervals))
  | `Unsat -> mk_false ark
  | `Unknown -> assert false

let abstract ?exists:(p=fun x -> true) ark man phi =
  let solver = Smt.mk_solver ark in
  let phi_symbols = symbols phi in
  let projected_symbols = Symbol.Set.filter (not % p) phi_symbols in
  let symbol_list = Symbol.Set.elements phi_symbols in
  let env_proj = ArkApron.Env.of_set ark (Symbol.Set.filter p phi_symbols) in

  let disjuncts = ref 0 in
  let rec go prop =
    solver#push ();
    solver#add [mk_not ark (ArkApron.formula_of_property prop)];
    match Log.time "lazy_dnf/sat" solver#get_model () with
    | `Unsat ->
      solver#pop 1;
      prop
    | `Unknown ->
      begin
        logf ~level:`warn "abstraction timed out (%d disjuncts); returning top"
          (!disjuncts);
        solver#pop 1;
        ArkApron.top man env_proj
      end
    | `Sat model -> begin
        let interp = Interpretation.of_model ark model symbol_list in
        let valuation = model#eval_real % (mk_const ark) in
        solver#pop 1;
        incr disjuncts;
        logf "[%d] abstract lazy_dnf" (!disjuncts);
        if (!disjuncts) = (!opt_abstract_limit) then begin
          logf ~level:`warn "Met symbolic abstraction limit; returning top";
          ArkApron.top man env_proj
        end else begin
          let disjunct =
            match Interpretation.select_implicant interp phi with
            | Some d -> Polyhedron.polyhedron_of_implicant ark d
            | None -> begin
                assert (model#sat phi);
                assert false
              end
          in
          let projected_disjunct =
            Polyhedron.local_project valuation projected_symbols disjunct
            |> Polyhedron.to_apron env_proj man
          in
          go (ArkApron.join prop projected_disjunct)
        end
      end
  in
  solver#add [phi];
  Log.time "Abstraction" go (ArkApron.bottom man env_proj)

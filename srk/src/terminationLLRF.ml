open Syntax
open BatPervasives
module Vec = Linear.QQVector
module IS = Iteration.Solver

include Log.Make(struct let name = "TerminationLLRF" end)

(* Given a formula F, find the weakest formula G such that G |= F and
   every quasi-ranking function of G is invariant.  Return None if G =
   false (i.e., F has a linear-lexicographic ranking function).  *)
let llrf_residual solver =
  let man = Polka.manager_alloc_loose () in
  let srk = IS.get_context solver in
  let abs_solver = IS.get_abstract_solver solver in
  let x_xp =
    Symbol.Set.fold
      (fun s xs -> (s,s)::xs)
      (IS.get_constants solver)
      (IS.get_symbols solver)
  in
  let pre =
    List.map (fun (x,_) -> mk_const srk x) x_xp
    |> Array.of_list
  in
  let diff =
    List.map (fun (x,x') -> mk_sub srk (mk_const srk x) (mk_const srk x')) x_xp
    |> Array.of_list
  in
  let dim = Array.length pre in
  let rec loop nb_invariants =
    let precondition =
      ConvexHull.abstract abs_solver ~man pre
    in
    if DD.is_bottom precondition then
      None (* Residual is inconsistent *)
    else
      (* Find the cone of quasi-ranking functions and strengthen F to
         constrain the generators of the cone to be invariant *)
      let non_inc_cone =
        ConvexHull.abstract abs_solver ~man diff
        |> Polyhedron.of_dd
        |> Polyhedron.dual_cone dim
        |> Polyhedron.dd_of ~man dim
      in
      let bounded_cone =
        let generators =
          precondition
          |> DD.enum_constraints
          |> BatEnum.map (fun (constraint_kind, v) ->
              let v = snd (Vec.pivot Linear.const_dim v) in
              match constraint_kind with
              | `Nonneg | `Pos -> (`Ray, v)
              | `Zero -> (`Line, v))
        in
        (* Origin must belong to the bounded terms cone *)
        BatEnum.push generators (`Vertex, Vec.zero);
        DD.of_generators dim generators
      in
      let qrf_cone = DD.meet non_inc_cone bounded_cone in
      let qrf_invariant =
        DD.enum_generators qrf_cone
        |> BatEnum.filter_map (fun (typ, vec) ->
               if typ = `Ray then
                 let diff_exp =
                   Linear.term_of_vec srk (Array.get diff) vec
                 in
                 Some (mk_eq srk diff_exp (mk_zero srk))
               else (* Only vertex is zero; lines are already invariant *)
                 None)
        |> BatList.of_enum
      in
      let nb_invariants' = List.length qrf_invariant in
      if nb_invariants' = nb_invariants then
        Some (Abstract.Solver.get_formula abs_solver) (* All QRFs are invariant *)
      else begin
        Abstract.Solver.add abs_solver qrf_invariant;
        loop nb_invariants'
      end
  in
  loop 0

let has_llrf solver = (llrf_residual solver = None)

let mp solver =
  let srk = IS.get_context solver in
  if has_llrf solver then mk_false srk else mk_true srk
